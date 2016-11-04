(* elpi: embedded lambda prolog interpreter                                  *)
(* copyright: 2014 - Enrico Tassi <enrico.tassi@inria.fr>                    *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

module F = Format

let debug = ref false
let dverbose = ref false
let where_loc = ref ("",0,max_int)
module M = Map.Make(String)
let cur_step = ref M.empty
let level = ref 0
let filter = ref []
let fonly = ref []
let hot = ref false
let hot_level = ref 0
let collect_perf = ref false
let trace_noprint = ref false

type perf_frame = {
  name : string;
  self : float;
  progeny : perf_frame M.t;
}

let perf_stack = ref [{name = "main"; self = 0.0; progeny = M.empty }]

let collect_perf_enter n =
  if !collect_perf then
  match !perf_stack with
  | { progeny } :: _ when M.mem n progeny ->
       perf_stack := M.find n progeny :: !perf_stack
  | _ ->
       perf_stack := { name = n; self = 0.0; progeny = M.empty } :: !perf_stack

let rec merge m1 m2 =
  M.fold (fun _ ({ name; self; progeny } as v) m ->
     try
       let { self = t; progeny = p } = M.find name m in
       M.add name { name; self = self +. t; progeny = merge progeny p } m
     with Not_found -> M.add name v m) m1 m2

let collect_perf_exit time =
  if !collect_perf then
  match !perf_stack with
  | { name = n1 } as top :: ({ name = n2} as prev) :: rest when n1 = n2 ->
      perf_stack := { name = n2;
                      self = prev.self; 
                      progeny = merge top.progeny prev.progeny } :: rest
  | top :: ({ progeny } as prev) :: rest ->
      let top = { top with self = top.self +. time } in
      perf_stack := { prev with progeny = M.add top.name top progeny } :: rest
  | _ -> assert false

let rec print_tree hot { name; self; progeny } indent =
  let tprogeny, (phot, thot) =
    M.fold (fun n { self } (x,(_,m as top)) ->
              x +. self, (if self > m then (n,self) else top))
      progeny (0.0,("",0.0)) in
  let phot =
    if thot *. 2.0 > tprogeny && M.cardinal progeny > 1 && indent < 6
    then phot else "" in
  Printf.eprintf "%s- %-20s %s %6.3f %6.3f %s\n"
    String.(make indent ' ' ) name String.(make (max 0 (20-indent)) ' ' )
    self (self -. tprogeny) (if name = hot then "!" else "");
  M.iter (fun _ t -> print_tree phot t (indent + 2)) progeny

let print_perf () =
  while List.length !perf_stack > 1 do collect_perf_exit 0.0; done;
  match !perf_stack with
  | [ { progeny } ] ->
        Printf.eprintf "  %-20s %s %6s %6s\n" "name"
          String.(make 20 ' ' ) "total" "self";
        Printf.eprintf "%s\n" (String.make 80 '-');
        M.iter (fun _ t -> print_tree "run" t 0) progeny
  | _ -> assert false

let () = at_exit (fun () -> if !collect_perf then print_perf ())

let get_cur_step k = try M.find k !cur_step with Not_found -> 0

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
    (* -trace-skip *)
    && (!fonly = [] || List.exists (fun p -> Str.string_match p k 0) !fonly)
    (* -trace-only *)
    && not(List.exists (fun p -> Str.string_match p k 0) !filter)

let init ?(where="",0,max_int) ?(skip=[]) ?(only=[]) ?(verbose=false) b =
  cur_step := M.empty;
  debug := b;
  dverbose := verbose;
  filter := List.map Str.regexp skip;
  fonly := List.map Str.regexp only;
  where_loc := where

let incr_cur_step k =
  let n = get_cur_step k in
  cur_step := M.add k (n+1) !cur_step

let make_indent () =
  String.make (max 0 (!level - !hot_level)) ' '

let print_enter k msg = 
  if not !trace_noprint then
    Format.eprintf "%s%s %d {{{@[<hov1> %a@]\n%!"
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
    Format.eprintf "%s %s =@[<hov1> %a@]\n%!" (make_indent ()) name f x

let printers = ref []

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

let print_exit k tailcall e time =
  if not !trace_noprint then
    Format.eprintf "%s}}} %s  (%.3fs)\n%!"
      (make_indent ()) (if tailcall then "->" else pr_exc e) time

let exit k tailcall ?(e=OK) time =
  if condition k then begin
    print_exit k tailcall e time;
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
        Printf.eprintf "stats@run %d: %s %s %d\n" step name key value)
      !logs
    end)

let usage =
  "\ntracing facility options:\n" ^
  "\t-trace-v  verbose\n" ^
  "\t-trace-at FUNCNAME START STOP  print trace between call START\n" ^
  "\t\tand STOP of function FNAME\n" ^
  "\t-trace-on  enable trace printing\n" ^
  "\t-trace-skip REX  ignore trace items matching REX\n" ^
  "\t-trace-only REX  trace only items matching REX\n" ^
  "\t-trace-maxbox NUM  Format max_boxes set to NUM\n" ^
  "\t-stats-on  Collect statistics\n" ^
  "\t-perf-on  Disable trace output, but keep perf\n" 
;;

let parse_argv argv =
  let on = ref false in
  let where = ref ("run",0,0) in
  let verbose = ref false in
  let skip = ref [] in
  let only = ref [] in
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
    | "-trace-maxbox" :: num :: rest ->
         Format.pp_set_max_boxes Format.err_formatter (int_of_string num);
         aux rest
    | "-perf-on" :: rest ->
         collect_perf := true; on := true; trace_noprint := true; aux rest
    | x :: rest -> x :: aux rest in
  let rest = aux (Array.to_list argv) in
  init ~where:!where ~verbose:!verbose ~only:!only ~skip:!skip !on;
  Array.of_list rest
;;

