(* A benchmark of elpi-lsp: the time to check a big document, compared with
   the time of the requests on the symbols (hover, highlight, semantic
   tokens). The functions of the server (Checker) are called directly: the
   time of the JSON messages is not counted.

   The document has [lines] lines: groups of a declaration and ten rules, each
   rule has two premises and three variables. The queries are at [queries]
   random positions (always the same ones). *)

let lines = 20_000
let rules = 10
let queries = 10_000

(* p<i> calls p<i-1>, in the premises the variables are permuted *)
let document () =
  let b = Buffer.create (lines * 40) in
  let groups = lines / (rules + 1) in
  for i = 0 to groups - 1 do
    Printf.bprintf b "pred p%d o:int, o:int, o:int.\n" i;
    let callee = if Int.equal i 0 then 0 else i - 1 in
    for j = 0 to rules - 1 do
      let x, y, z = match j mod 3 with 0 -> "X", "Y", "Z" | 1 -> "Y", "Z", "X" | _ -> "Z", "X", "Y" in
      Printf.bprintf b "p%d X Y Z :- p%d %s %s %s, p%d %s %s %s.\n" i callee x y z callee z y x
    done
  done;
  Buffer.contents b

let time f =
  let t = Unix.gettimeofday () in
  let r = f () in
  r, Unix.gettimeofday () -. t

(* the rows of the table of the results *)
type row = { what : string; count : int; total : float; answered : int option }

let print_table ~t_check rows =
  let header = [ "request"; "count"; "total (s)"; "each (us)"; "answered"; "% of check" ] in
  let cells { what; count; total; answered } = [
    what; string_of_int count; Printf.sprintf "%.3f" total;
    Printf.sprintf "%.1f" (total /. float count *. 1e6);
    (match answered with Some n -> string_of_int n | None -> "-");
    Printf.sprintf "%.1f" (total /. t_check *. 100.) ] in
  let table = header :: List.map cells rows in
  let widths = List.fold_left (fun ws r -> List.map2 (fun w c -> max w (String.length c)) ws r)
      (List.map (fun _ -> 0) header) table in
  (* the first column is aligned on the left, the numbers on the right *)
  let line r = String.concat "  " (List.mapi (fun i (w, c) ->
      if Int.equal i 0 then Printf.sprintf "%-*s" w c else Printf.sprintf "%*s" w c) (List.combine widths r)) in
  print_endline (line header);
  print_endline (String.concat "  " (List.map (fun w -> String.make w '-') widths));
  List.iter (fun r -> print_endline (line r)) (List.tl table)

let () =
  let path = Filename.concat (Sys.getcwd ()) "perf.elpi" in
  (* the units before the document (the standard library) are compiled once
     and cached by the server, for the instance of the document: they are
     compiled here, before measuring *)
  let instance = Checker.new_instance () in
  ignore (Checker.check ~instance ~path:(Filename.concat (Sys.getcwd ()) "warmup.elpi") "pred w.\nw.\n");
  let text = document () in
  let n_lines = List.length (String.split_on_char '\n' text) - 1 in
  Printf.printf "document: %d lines, %d bytes\n%!" n_lines (String.length text);
  let { Checker.diagnostics; hover }, t_check = time (fun () -> Checker.check ~instance ~path text) in
  Printf.printf "diagnostics: %d\n%!" (List.length diagnostics);
  List.iteri (fun i (d : Checker.diagnostic) ->
      if i < 5 then Printf.printf "  %d-%d: %s\n" d.start d.stop d.message) diagnostics;
  let hover = match hover with Some h -> h | None -> failwith "the parser failed on the document" in
  let rand = Random.State.make [| 42 |] in
  let offsets = Array.init queries (fun _ -> Random.State.int rand (String.length text)) in
  (* the information for the requests (LSP.hover) is computed when first
     needed, by the first request, whichever it is *)
  let first what f =
    let _, total = time f in
    { what = "first " ^ what; count = 1; total; answered = None } in
  let first_highlight = first "highlight" (fun () -> Checker.highlights_at ~path offsets.(0) hover) in
  let first_hover = first "hover" (fun () -> Checker.hover_at ~path ~text offsets.(0) hover) in
  let many what answered =
    let answered, total = time (fun () -> Array.fold_left (fun n off -> if answered off then n + 1 else n) 0 offsets) in
    { what; count = queries; total; answered = Some answered } in
  let hovers = many "hover" (fun off -> Option.is_some (Checker.hover_at ~path ~text off hover)) in
  let highlights = many "highlight" (fun off -> Checker.highlights_at ~path off hover <> []) in
  let tokens, total = time (fun () -> Checker.semantic_tokens ~path (Text.make text) hover) in
  let tokens = { what = Printf.sprintf "semantic tokens (%d)" (Array.length tokens / 5); count = 1; total; answered = None } in
  print_newline ();
  print_table ~t_check [
    { what = "check"; count = 1; total = t_check; answered = None };
    first_highlight; first_hover; hovers; highlights; tokens ]
