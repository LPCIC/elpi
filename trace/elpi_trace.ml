(* elpi: embedded lambda prolog interpreter                                  *)
(* copyright: 2014 - 2017 Enrico Tassi <enrico.tassi@inria.fr>               *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module F = Format

let err_fmt = ref F.err_formatter
let set_formatter x = err_fmt := x
let eprintf x = F.fprintf !err_fmt x
let set_formatter_maxcols i = F.pp_set_margin !err_fmt i
let set_formatter_maxbox i = F.pp_set_max_boxes !err_fmt i

module StrMap = Map.Make(String)
module Str = Re.Str

let debug = ref false
let dverbose = ref false
let where_loc = ref ("",0,max_int)
let cur_step = ref StrMap.empty
let level = ref 0
let filter = ref []
let fonly = ref []
let ponly = ref []
let hot = ref false
let hot_level = ref 0
let collect_perf = ref false
let trace_noprint = ref false
let cur_pred = ref None

type perf_frame = {
  name : string;
  self : float;
  progeny : perf_frame StrMap.t;
}

let perf_stack = ref [{name = "main"; self = 0.0; progeny = StrMap.empty }]

let collect_perf_enter n =
  if !collect_perf then
  match !perf_stack with
  | { progeny; _ } :: _ when StrMap.mem n progeny ->
       perf_stack := StrMap.find n progeny :: !perf_stack
  | _ ->
       perf_stack := { name = n; self = 0.0; progeny = StrMap.empty } :: !perf_stack

let rec merge m1 m2 =
  StrMap.fold (fun _ ({ name; self; progeny } as v) m ->
     try
       let { self = t; progeny = p; _ } = StrMap.find name m in
       StrMap.add name { name; self = self +. t; progeny = merge progeny p } m
     with Not_found -> StrMap.add name v m) m1 m2

let collect_perf_exit time =
  if !collect_perf then
  match !perf_stack with
  | { name = n1; _ } as top :: ({ name = n2; _ } as prev) :: rest when n1 = n2 ->
      perf_stack := { name = n2;
                      self = prev.self; 
                      progeny = merge top.progeny prev.progeny } :: rest
  | top :: ({ progeny; _ } as prev) :: rest ->
      let top = { top with self = top.self +. time } in
      perf_stack := { prev with progeny = StrMap.add top.name top progeny } :: rest
  | _ -> assert false

let rec print_tree hot { name; self; progeny } indent =
  let tprogeny, (phot, thot) =
    StrMap.fold (fun n { self; _ } (x,(_,m as top)) ->
              x +. self, (if self > m then (n,self) else top))
      progeny (0.0,("",0.0)) in
  let phot =
    if thot *. 2.0 > tprogeny && StrMap.cardinal progeny > 1 && indent < 6
    then phot else "" in
  eprintf "%s- %-20s %s %6.3f %6.3f %s\n"
    String.(make indent ' ' ) name String.(make (max 0 (20-indent)) ' ' )
    self (self -. tprogeny) (if name = hot then "!" else "");
  StrMap.iter (fun _ t -> print_tree phot t (indent + 2)) progeny

let print_perf () =
  while List.length !perf_stack > 1 do collect_perf_exit 0.0; done;
  match !perf_stack with
  | [ { progeny; _ } ] ->
        eprintf "  %-20s %s %6s %6s\n" "name"
          String.(make 20 ' ' ) "total" "self";
        eprintf "%s\n" (String.make 80 '-');
        StrMap.iter (fun _ t -> print_tree "run" t 0) progeny
  | _ -> assert false

let () = at_exit (fun () -> if !collect_perf then print_perf ())

let get_cur_step k = try StrMap.find k !cur_step with Not_found -> 0

let condition k =
  (* -trace-on *)
  !debug &&
    (* -trace-at *)
    let loc, first_step, last_step = !where_loc in
    ((!hot && k <> loc) ||
       (k = loc &&
       let cur_step = get_cur_step k in
       hot := cur_step >= first_step && cur_step <= last_step;
       if !hot && !hot_level = 0 then hot_level := !level;
       !hot))
    (* -trace-only *)
    && (!fonly = [] || List.exists (fun p -> Str.string_match p k 0) !fonly)
    (* -trace-skip *)
    && not(List.exists (fun p -> Str.string_match p k 0) !filter)
    (* -trace-only-pred *)
    && (match !cur_pred with
        | None -> true
        | Some pred ->
            !ponly = [] ||
            List.exists (fun p -> Str.string_match p pred 0) !ponly)

let init ?(where="",0,max_int) ?(skip=[]) ?(only=[]) ?(only_pred=[]) ?(verbose=false) b =
  cur_step := StrMap.empty;
  debug := b;
  dverbose := verbose;
  filter := List.map Str.regexp skip;
  fonly := List.map Str.regexp only;
  ponly := List.map Str.regexp only_pred;
  where_loc := where;
  level := 0;
  hot := false;
  hot_level := 0
;;

let incr_cur_step k =
  let n = get_cur_step k in
  cur_step := StrMap.add k (n+1) !cur_step

let make_indent () =
  String.make (max 0 (!level - !hot_level)) ' '

let print_enter k msg = 
  if not !trace_noprint then
    eprintf "%s%s %d {{{@[<hov1> %a@]\n%!"
      (make_indent ()) k (get_cur_step k) (fun fmt () -> msg fmt) ()

let enter k msg =
  incr level;
  incr_cur_step k;
  if condition k then begin
    print_enter k msg;
    collect_perf_enter k;
  end

let print name f x = 
 if not !trace_noprint && condition name then
    eprintf "%s %s =@[<hov1> %a@]\n%!" (make_indent ()) name f x

let printers = ref []

let cur_pred p = cur_pred := p

exception Unknown
exception OK

let pr_exc = function
  | OK -> "ok"
  | e ->
     let rec aux = function
       | [] -> "error: " ^Printexc.to_string e
       | f :: fs ->
             try f e
             with Unknown -> aux fs in
     aux !printers
let pr_exn f = printers := f :: !printers

exception TREC_CALL of Obj.t * Obj.t (* ('a -> 'b) * 'a *)

let print_exit tailcall e time =
  if not !trace_noprint then
    eprintf "%s}}} %s  (%.3fs)\n%!"
      (make_indent ()) (if tailcall then "->" else pr_exc e) time

let exit k tailcall ?(e=OK) time =
  if condition k then begin
    print_exit tailcall e time;
    collect_perf_exit time;
  end;
  decr level

(* we should make another file... *)
let collecting_stats = ref false
let logs = ref []
let log name key value =
  if !collecting_stats then
    logs := (name,key,get_cur_step "run",value) :: !logs
let () = 
  at_exit (fun () ->
    if !logs != [] then begin
      List.iter (fun (name,key,step,value) ->
        eprintf "stats@run %d: %s %s %d\n" step name key value)
      !logs
    end)

let usage =
  "\nTracing options can be used to debug your programs and Elpi as well.\n" ^
  "A sensible set of options to debug your programs is\n" ^
  "  -trace-on -trace-at run 1 9999\n" ^
  "  -trace-only run -trace-only select -trace-only assign\n" ^
  "Tracing options:\n" ^
  "\t-trace-v  verbose\n" ^
  "\t-trace-at FUNCNAME START STOP  print trace between call START\n" ^
  "\t\tand STOP of function FNAME\n" ^
  "\t-trace-on  enable trace printing\n" ^
  "\t-trace-skip REX  ignore trace items matching REX\n" ^
  "\t-trace-only REX  trace only items matching REX\n" ^
  "\t-trace-only-pred REX  trace only when the current predicate matches REX\n" ^
  "\t-trace-maxbox NUM  Format max_boxes set to NUM\n" ^
  "\t-trace-maxcols NUM  Format margin set to NUM\n" ^
  "\t-stats-on  Collect statistics\n" ^
  "\t-perf-on  Disable trace output, but keep perf\n" 
;;

let parse_argv argv =
  let on = ref false in
  let where = ref ("run",0,0) in
  let verbose = ref false in
  let skip = ref [] in
  let only = ref [] in
  let only_pred = ref [] in
  let rec aux = function
    | [] -> []
    | "-trace-v" :: rest -> verbose := true; aux rest
    | "-trace-at" :: fname :: start :: stop :: rest ->
         where := (fname, int_of_string start, int_of_string stop);
         aux rest
    | "-trace-on" :: rest -> trace_noprint := false; on := true; aux rest
    | "-stats-on" :: rest -> collecting_stats := true; aux rest
    | "-trace-skip" :: expr :: rest ->
         skip := expr :: !skip;
         aux rest
    | "-trace-only" :: expr :: rest ->
         only := expr :: !only;
         aux rest
    | "-trace-only-pred" :: pname :: rest ->
         only_pred := pname :: !only_pred;
         aux rest;
    | "-trace-maxbox" :: num :: rest ->
         set_formatter_maxbox (int_of_string num);
         aux rest
    | "-trace-maxcols" :: num :: rest ->
         set_formatter_maxcols (int_of_string num);
         aux rest
    | "-perf-on" :: rest ->
         collect_perf := true; on := true; trace_noprint := true; aux rest
    | x :: rest -> x :: aux rest in
  let rest = aux argv in
  init ~where:!where ~verbose:!verbose ~only:!only
       ~only_pred:!only_pred ~skip:!skip !on;
  rest
;;

