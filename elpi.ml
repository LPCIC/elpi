open Lprun
open Lpdata

let set_terminal_width () =
  let ic, _ as p = Unix.open_process "tput cols" in
  let w = int_of_string (input_line ic) in
  let _ = Unix.close_process p in
  Format.pp_set_margin Format.err_formatter w;
  Format.pp_set_ellipsis_text Format.err_formatter "...";
  Format.pp_set_max_boxes Format.err_formatter 30;
;;

let type_err name exp got =
  Format.eprintf "Wrong call to %s, %s expected, got %a\n%!"
    name exp (LP.prf_data []) got; exit 1

let protect f x = try f x with UnifFail _ -> raise NoClause

let check_list2 name t =
  match LP.look t with
  | LP.Seq (l,tl) when L.len l = 2 && LP.equal tl LP.mkNil -> L.hd l, L.get 1 l
  | _ -> type_err name "list of len 2" t

let check_string name t =
  match LP.look t with
  | LP.Ext x when isString x -> getString x
  | _ -> type_err name "string" t

let extern_kv name f =
  register_custom name (fun t s ->
    let t, s = Red.nf t s in
    let k, v = check_list2 name t in
    let k = check_string name k in
    protect (f k v) s)
;;

let extern_k name f =
  register_custom name (fun t s ->
    let t, s = Red.nf t s in
    let k = check_string name t in
    protect (f k) s)
;;

let register_trace () =
  extern_kv "trace_counter" (fun name value s ->
    let n = Trace.get_cur_step name in
    protect (unify (LP.mkExt (mkString (string_of_int n))) value) s)
;;

let register_imperative_counters () =
  let module M = Map.Make(struct type t = string let compare = compare end) in
  let counters = ref M.empty in
  extern_k "incr" (fun name s ->
    try counters := M.add name (M.find name !counters + 1) !counters; s
    with Not_found -> counters := M.add name 1 !counters; s);
  extern_k "reset" (fun name s -> counters := M.add name 0 !counters; s);
  extern_kv "get" (fun name value s ->
    let n = try M.find name !counters with Not_found -> 0 in
    protect (unify (LP.mkExt (mkString (string_of_int n))) value) s)
;;

let register_exit_abort () =
  let aborts = ref 0 in
  extern_k "abort" (fun text s ->
    incr aborts; if !aborts = int_of_string text then exit 1 else s);
  extern_k "exit" (fun text s -> exit (int_of_string text));
;;

let register_parser () =
  extern_kv "parse" (fun text value s ->
    protect (unify (LP.parse_data text) value) s);
  register_custom "read" (fun t s ->
    let input = input_line stdin in
    protect (unify (LP.mkExt (mkString input)) t) s);
;;

let register_print () =
  let print_atom s t =
    let unescape s =
      Str.global_replace (Str.regexp_string "\\n") "\n"
      (Str.global_replace (Str.regexp_string "\\t") "\t"
        s) in
    let t, s = Red.nf t s in
    match LP.look t with
    | LP.Ext t  when isString t ->
        Format.eprintf "%s%!" (unescape (getString t))
    | _ -> Format.eprintf "%a%!" (LP.prf_data []) t in
  register_custom "print" (fun t s -> print_atom s t; s);
  register_custom "printl" (fun t s ->
    let t, s = Red.nf t s in
    match LP.look t with
    | LP.Seq(l,_) ->
        List.iter (print_atom s) (L.to_list l); Format.eprintf "\n%!"; s
    | _ -> type_err "printl" "list" t);
;;

let _ = Printexc.record_backtrace true
let _ =
  let control = Gc.get () in
  let tweaked_control = { control with
    Gc.minor_heap_size = 33554432; (** 4M *)
    Gc.space_overhead = 120;
  } in
  Gc.set tweaked_control;
  set_terminal_width ();
  register_print ();
  register_custom "is_flex" (fun t s ->
    let t, s = Red.whd t s in
    match LP.look t with
    | LP.Uv _ -> s
    | LP.App xs ->
        (match LP.look (L.hd xs) with LP.Uv _ -> s | _ -> raise NoClause)
    | _ -> raise NoClause);
  register_exit_abort ();
  register_imperative_counters ();
  register_trace ();
  register_parser ();
  register_custom "zero_level" (fun t s ->
    let h, s = Subst.fresh_uv 0 s in
    protect (unify t h) s);
;;

let test_prog p g =
 let width = Format.pp_get_margin Format.err_formatter () in
 for i = 0 to width - 1 do Format.eprintf "-"; done;
 Format.eprintf "@\n%!";
 try
  let p = LP.parse_program p in
  let g = LP.parse_goal g in
  (*Format.eprintf "@[<hv2>program:@ %a@]@\n%!" LP.prf_program p;*)
  let rec aux (g,assignments,s,dgs,continuation) =
   (*Format.eprintf
     "@\n@[<hv2>output:@ %a@]@\n@[<hv2>nf out:@ %a@]@\n@[<hv2>subst:@ %a@]@\n%!"
     (LP.prf_goal []) (Subst.apply_subst_goal s g) 
     (LP.prf_goal []) (LP.map_premise (Red.nf s) g)
     Subst.prf_subst s;*)
   Format.eprintf
     "@\n@[<hv2>input:@ %a@]@\n%!"
     (LP.prf_goal []) (fst(Red.nf g (Subst.empty 0)));
   List.iter (fun x ->
    Format.eprintf "@[<hv2>%a@ = %a@]@\n%!"
     (LP.prf_data []) x (LP.prf_data []) (fst(Red.nf x s)))
     assignments;
   List.iter (fun (g,eh) ->
    Format.eprintf "delay: @[<hv>%a@ |- %a@]\n%!"
     (LP.prf_program ~compact:false)
     (List.map (function i,k,p,u -> i,k,fst(Red.nf p s),u) eh)
     (LP.prf_goal []) (fst(Red.nf g s))) dgs;
   Printf.printf "next? (Y/n)> %!";
   let l = input_line stdin in
   if l = "y" || l = "" then
    try aux (next continuation)
    with Lprun.NoClause ->
     Printf.printf "no more solutions\n";
     exit 0
   else exit 0
  in
   aux (run_dls p g)
 with Stream.Error msg ->
   Format.eprintf "@[Parse error: %s@]@\n%!" msg
;;

let _ =
  let argv = Trace.parse_argv Sys.argv in
  for i=1 to Array.length argv - 1 do
    Printf.eprintf "running with %s\n" argv.(i);
    let p =
      let b = Buffer.create 1024 in
      let ic = open_in argv.(i) in
      try
        while true do Buffer.add_string b (input_line ic^"\n") done;
        assert false
      with End_of_file -> Buffer.contents b in
    let g =
      Printf.printf "goal> %!";
      input_line stdin in
    test_prog p g
  done;
  Trace.quit ()

