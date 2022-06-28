(* elpi: embedded lambda prolog interpreter                                  *)
(* copyright: 2014 - 2017 Enrico Tassi <enrico.tassi@inria.fr>               *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module F = Format

module IntMap = Map.Make(struct type t = int let compare x y = x - y end)
module StrMap = Map.Make(String)
module Str = Re.Str

let debug = ref false
let where_loc = ref ("",0,max_int)
let cur_step = ref IntMap.empty
let filter = ref []
let fonly = ref []
let ponly = ref []
let hot = ref false
let collect_perf = ref false
let trace_noprint = ref false
let cur_pred = ref None

type message_kind = Start | Stop of { cause : string; time : float } | Info
type j = J : (F.formatter -> 'a -> unit) * 'a -> j
type message = {
  runtime_id : int;
  goal_id : int;
  kind : message_kind;
  name : string;
  step : int;
  payload : j list;
}

let printer : (message -> unit) ref = ref (fun _ -> assert false)

module Perf = struct

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

let rec print_tree fmt hot { name; self; progeny } indent =
  let tprogeny, (phot, thot) =
    StrMap.fold (fun n { self; _ } (x,(_,m as top)) ->
              x +. self, (if self > m then (n,self) else top))
      progeny (0.0,("",0.0)) in
  let phot =
    if thot *. 2.0 > tprogeny && StrMap.cardinal progeny > 1 && indent < 6
    then phot else "" in
  F.fprintf fmt "%s- %-20s %s %6.3f %6.3f %s\n"
    String.(make indent ' ' ) name String.(make (max 0 (20-indent)) ' ' )
    self (self -. tprogeny) (if name = hot then "!" else "");
  StrMap.iter (fun _ t -> print_tree fmt phot t (indent + 2)) progeny

let print_perf () =
  while List.length !perf_stack > 1 do collect_perf_exit 0.0; done;
  let stack =
    match !perf_stack with
    | [ { progeny; _ } ] -> progeny
    | _ -> assert false in
  let payload fmt =
    F.fprintf fmt "  %-20s %s %6s %6s\n" "name"
      String.(make 20 ' ' ) "total" "self";
    F.fprintf fmt "%s\n" (String.make 80 '-');
    StrMap.iter (fun _ t -> print_tree fmt "run" t 0) stack;
    F.pp_print_flush fmt () in
  !printer { runtime_id = 0; kind = Info; goal_id = 0; name = "perf"; step = 0; payload = [J((fun fmt () -> payload fmt),())] }

let () = at_exit (fun () -> if !collect_perf then print_perf ())

end

module Trace = struct

let get_cur_step ~runtime_id k =
  try
    let m = IntMap.find runtime_id !cur_step in
    try StrMap.find k m
    with Not_found ->
    try StrMap.find "run" m
    with Not_found -> 0
  with Not_found -> 0

let condition ~runtime_id k =
  (* -trace-on *)
  !debug &&
    (* -trace-at *)
    let loc, first_step, last_step = !where_loc in
    ((!hot && k <> loc) ||
       (k = loc &&
       let cur_step = get_cur_step ~runtime_id k in
       hot := cur_step >= first_step && cur_step <= last_step;
       !hot) ||
    (get_cur_step ~runtime_id:0 "run" = 0 && first_step = 0 && k = "user:newgoal"))
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

let init ?(where="",0,max_int) ?(skip=[]) ?(only=[]) ?(only_pred=[]) b =
  cur_step := IntMap.empty;
  debug := b;
  filter := List.map Str.regexp skip;
  fonly := List.map Str.regexp only;
  ponly := List.map Str.regexp only_pred;
  where_loc := where;
  hot := false;
;;

let incr_cur_step ~runtime_id k =
  let n = get_cur_step ~runtime_id k in
  let n = n + 1 in
  try
    let m = IntMap.find runtime_id !cur_step in
    let m = StrMap.add k n m in
    cur_step := IntMap.add runtime_id m !cur_step
  with Not_found ->
    let m = StrMap.empty in
    let m = StrMap.add k n m in
    cur_step := IntMap.add runtime_id m !cur_step


end

let enter ~runtime_id k payload =
  Trace.incr_cur_step ~runtime_id k;
  if Trace.condition ~runtime_id k then begin
    Perf.collect_perf_enter k;
    if not !trace_noprint then
      !printer { runtime_id; goal_id = 0; name = k; step = Trace.get_cur_step ~runtime_id k; kind = Start; payload = [J((fun fmt () -> payload fmt),())] }
  end

let info ~runtime_id ?(goal_id=0) k payload =
 if not !trace_noprint && Trace.condition ~runtime_id k then
   !printer { runtime_id; goal_id ; name = k; step = Trace.get_cur_step ~runtime_id k; kind = Info; payload }


exception TREC_CALL of Obj.t * Obj.t (* ('a -> 'b) * 'a *)
exception OK

let pr_exc = function
  | OK -> "ok"
  | e ->"error: " ^Printexc.to_string e

let exit ~runtime_id k tailcall e time =
  let e = match e with None -> OK | Some x -> x in
  if Trace.condition ~runtime_id k then begin
    Perf.collect_perf_exit time;
    if not !trace_noprint then
      !printer { runtime_id; goal_id = 0; name = k; step = Trace.get_cur_step ~runtime_id k; kind = Stop { cause = (if tailcall then "->" else pr_exc e); time }; payload = [J((fun _ _ -> ()),())] }
  end

(* Json *)
let pp_s fmt s =
  Format.fprintf fmt "%S" s

let pp_i fmt i =
  Format.fprintf fmt "%d" i

let pp_f fmt f =
  Format.fprintf fmt "%f" f

let pp_kv fmt = function
  | k, J(pp_v, v) -> F.fprintf fmt "%a : %a" pp_s k pp_v v

let pp_j fmt = function
  | J(pp,x) -> pp fmt x

let rec pp_comma_l fmt pp = function
  | [] -> ()
  | x :: xs -> F.fprintf fmt ","; pp fmt x; pp_comma_l fmt pp xs

let pp_a fmt (l : j list) =
  F.fprintf fmt "[";
  begin match l with
  | [] -> ()
  | x :: l -> pp_j fmt x; pp_comma_l fmt pp_j l
  end;
  F.fprintf fmt "]"


module JSON_STRING_ENCODING = struct
  (* This code is from Yojson *)

  let hex n =
    Char.chr (
      if n < 10 then n + 48
      else n + 87
    )
  
  let write_special src start stop ob str =
    Buffer.add_substring ob src !start (stop - !start);
    Buffer.add_string ob str;
    start := stop + 1
  
  let write_control_char src start stop ob c =
    Buffer.add_substring ob src !start (stop - !start);
    Buffer.add_string ob "\\u00";
    Buffer.add_char ob (hex (Char.code c lsr 4));
    Buffer.add_char ob (hex (Char.code c land 0xf));
    start := stop + 1
  
  let finish_string src start ob =
    try
      Buffer.add_substring ob src !start (String.length src - !start)
    with exc ->
      Printf.eprintf "src=%S start=%i len=%i\n%!"
        src !start (String.length src - !start);
      raise exc
  
  let write_string_body ob s =
    let start = ref 0 in
    for i = 0 to String.length s - 1 do
      match s.[i] with
          '"' -> write_special s start i ob "\\\""
        | '\\' -> write_special s start i ob "\\\\"
        | '\b' -> write_special s start i ob "\\b"
        | '\012' -> write_special s start i ob "\\f"
        | '\n' -> write_special s start i ob "\\n"
        | '\r' -> write_special s start i ob "\\r"
        | '\t' -> write_special s start i ob "\\t"
        | '\x00'..'\x1F'
        | '\x7F' as c -> write_control_char s start i ob c
        | _ -> ()
    done;
    finish_string s start ob

end

let pp_as fmt (l : j list) =
  let pp_j fmt x =
    let s = F.asprintf "%a" pp_j x in
    let b = Buffer.create 64 in
    JSON_STRING_ENCODING.write_string_body b s;
    F.fprintf fmt "\"%s\"" (Buffer.contents b) in
  F.fprintf fmt "[";
  begin match l with
  | [] -> ()
  | x :: l ->
     pp_j fmt x;
     pp_comma_l fmt pp_j l
  end;
  F.fprintf fmt "]"


let pp_d fmt (l : (string * j) list) =
  F.fprintf fmt "{";
  begin match l with
  | [] -> ()
  | x :: l -> pp_kv fmt x; pp_comma_l fmt pp_kv l
  end;
  F.fprintf fmt "}"

let pp_kind fmt = function
  | Start -> pp_a fmt [J(pp_s,"Start")]
  | Info -> pp_a fmt [J(pp_s,"Info")]
  | Stop { cause; time } -> pp_a fmt [J(pp_s,"Stop");J(pp_s,cause);J(pp_f,time)]

let print_json fmt  = (); fun { runtime_id; goal_id; kind; name; step; payload } ->
  pp_d fmt [
    "step", J(pp_i,step);
    "kind", J(pp_kind,kind);
    "goal_id", J(pp_i,goal_id);
    "runtime_id", J(pp_i,runtime_id);
    "name", J(pp_s,name);
    "payload", J(pp_as, payload)
  ];
  F.pp_print_newline fmt ();
  F.pp_print_flush fmt ()

(* TTY *)
let tty_formatter_maxcols = ref 80
let tty_formatter_maxbox = ref max_int
let set_tty_formatter_maxcols i = tty_formatter_maxcols := i
let set_tty_formatter_maxbox i = tty_formatter_maxbox := i

let pplist ppelem f l =
    F.fprintf f "@[<v>";
    List.iter (fun x -> F.fprintf f "%a%s@," ppelem x " ") l;
    F.fprintf f "@]"
;;

let print_tty fmt = (); fun { runtime_id; goal_id; kind; name; step; payload } ->
  match kind with
  | Start ->
    F.fprintf fmt "%s %d {{{@[<hov1> %a@]\n%!" name step (pplist pp_j) payload
  | Stop { cause; time } ->
    F.fprintf fmt "}}} %s  (%.3fs)\n%!" cause time
  | Info ->
    F.fprintf fmt "  rid:%d step:%d gid:%d %s =@[<hov1> %a@]\n%!" runtime_id step goal_id name (pplist pp_j) payload

let () = printer := print_tty F.err_formatter

type trace_format = TTY | JSON
let set_trace_output format formatter =
  match format with
  | TTY ->
      F.pp_set_max_boxes formatter !tty_formatter_maxbox;
      F.pp_set_margin formatter !tty_formatter_maxcols;
      printer := print_tty formatter
  | JSON ->
      printer := print_json formatter

let output_file = ref None

let end_trace ~runtime_id =
  if runtime_id = 0 then
    match !output_file with
    | None -> ()
    | Some(`File(tmp,final)) -> Sys.rename tmp final
    | Some(`Socket i) -> Unix.close i

let fmt_of_file s =
  try
         if s = "stdout" then F.std_formatter
    else if s = "stderr" then F.err_formatter
    else if s.[0] = '/' || s.[0] = '.' then begin
      let file = s in
      let tmp_file = s ^".tmp" in
      output_file := Some (`File(tmp_file,file));
      F.formatter_of_out_channel (open_out tmp_file)
    end else
        let n = String.index s ':' in
        let host = String.sub s 0 n in
        let port = String.sub s (n+1) (String.length s - n - 1) in
        let open Unix in
        match getaddrinfo host port [AI_FAMILY PF_INET;AI_SOCKTYPE SOCK_STREAM] with
        | [] -> raise Not_found
        | { ai_family ; ai_socktype ; ai_protocol ; ai_addr; _ } :: _ ->
            let s = socket ai_family ai_socktype ai_protocol in
            Unix.connect s ai_addr;
            output_file := Some (`Socket s);
            F.formatter_of_out_channel (Unix.out_channel_of_descr s)
  with e ->
     Printf.eprintf "error: %s\n" (Printexc.to_string e);
     F.err_formatter

let set_trace_output_file format file =
  let formatter = fmt_of_file file in
  set_trace_output format formatter 

(* we should make another file... *)
let collecting_stats = ref false
let logs = ref []
let log ~runtime_id name key value =
  if !collecting_stats then
    logs := (name,key,Trace.get_cur_step ~runtime_id "run",value) :: !logs

let () =
  at_exit (fun () ->
    if !logs != [] then begin
      List.iter (fun (name,key,step,value) ->
        !printer {
           kind = Info; name = name; step = step;
           goal_id = 0; runtime_id = 0; payload = [J((fun fmt () ->
             F.fprintf fmt "%s = %d" key value),())] })
      !logs
    end)

let usage = {|
Tracing options:
        -trace-at FNAME START STOP  print trace between call START
         and STOP of function FNAME (FNAME can be omitted, default is run)
        -trace-on KIND FILE enable trace printing.
          KIND is tty or json (default is tty).
          FILE is stdout or stderr (default) or host:port or /path or ./path
        -trace-skip REX  ignore trace items matching REX
        -trace-only REX  trace only items matching REX
        -trace-only-pred REX  trace only when the current predicate matches REX
        -trace-tty-maxbox NUM  Format max_boxes set to NUM
        -trace-tty-maxcols NUM  Format margin set to NUM
        -stats-on  Collect statistics
        -perf-on  Disable trace output, but keep perf

Tracing options can be used to debug your programs and the Elpi interpreter.
Tracing points for the user are prefixed with 'user:' while the ones
for the Elpi developer with 'dev:'. A sensible set of options to debug your
programs is: -trace-on -trace-at 1 9999 -trace-only '\(run\|select\|user:\)'
|}
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
       if Str.(string_match (regexp "[0-9]+") fname 0) then begin
         where := ("run", int_of_string fname, int_of_string start);
         aux (stop :: rest)
       end else begin
         where := (fname, int_of_string start, int_of_string stop);
         aux rest
       end
    | "-trace-on" :: "tty" :: file :: rest ->
         set_trace_output_file TTY file;
         trace_noprint := false; on := true; aux rest
    | "-trace-on" :: "json" :: file :: rest ->
         set_trace_output_file JSON file;
         trace_noprint := false; on := true; aux rest
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
    | "-trace-tty-maxbox" :: num :: rest ->
         set_tty_formatter_maxbox (int_of_string num);
         aux rest
    | "-trace-tty-maxcols" :: num :: rest ->
         set_tty_formatter_maxcols (int_of_string num);
         aux rest
    | "-perf-on" :: rest ->
         collect_perf := true; on := true; trace_noprint := true; aux rest
    | x :: rest -> x :: aux rest in
  let rest = aux argv in
  Trace.init ~where:!where ~only:!only
       ~only_pred:!only_pred ~skip:!skip !on;
  rest
;;

let set_cur_pred x = cur_pred := x
let get_cur_step ~runtime_id x = Trace.get_cur_step ~runtime_id x