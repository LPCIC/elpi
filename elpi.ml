open Lprun
open Lpdata

let set_terminal_width ?(max_w=
    let ic, _ as p = Unix.open_process "tput cols" in
    let w = int_of_string (input_line ic) in
    let _ = Unix.close_process p in w) () =
  Format.pp_set_margin Format.err_formatter max_w;
  Format.pp_set_ellipsis_text Format.err_formatter "...";
  Format.pp_set_max_boxes Format.err_formatter 30;
;;

let type_err name exp got =
  Format.eprintf "Wrong call to %s, %s expected, got %a\n%!"
    name exp (LP.prf_data []) got; exit 1

let protect f x = try f x with UnifFail _ -> raise NoClause

let check_list1 name t =
  match LP.look t with
  | LP.Seq (l,tl) when L.len l = 1 && LP.equal tl LP.mkNil -> L.hd l
  | _ -> type_err name "list of len 1" t

let check_list2 name t =
  match LP.look t with
  | LP.Seq (l,tl) when L.len l = 2 && LP.equal tl LP.mkNil -> L.hd l, L.get 1 l
  | _ -> type_err name "list of len 2" t

let check_list name t =
  match LP.look t with
  | LP.Seq (l,tl) when LP.equal tl LP.mkNil -> L.to_list l
  | _ -> type_err name "list" t

let check_string name t =
  match LP.look t with
  | LP.Ext x when isString x -> getString x
  | _ -> type_err name "string" t

let extern_vv name f =
  register_custom_predicate name (fun t s ->
    let t, s = Red.nf t s in
    let v1, v2 = check_list2 name t in
    protect (f v1 v2) s)
;;

let extern_kv name f =
  register_custom_predicate name (fun t s ->
    let t, s = Red.nf t s in
    let k, v = check_list2 name t in
    let k = check_string name k in
    protect (f k v) s)
;;

let extern_k name f =
  register_custom_predicate name (fun t s ->
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
  register_custom_predicate "read" (fun t s ->
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
  register_custom_predicate "print" (fun t s -> print_atom s t; s);
  register_custom_predicate "printl" (fun t s ->
    let t, s = Red.nf t s in
    match LP.look t with
    | LP.Seq(l,_) ->
        List.iter (print_atom s) (L.to_list l); Format.eprintf "\n%!"; s
    | _ -> type_err "printl" "list" t);
;;

let register_frozen_tab () =
  extern_vv "set-frozen-info" (fun frozen value s ->
    assert(LP.collect_hv value = [] && LP.collect_Uv value = []);
    let rec aux frozen =
      match LP.look frozen with
      | LP.Con(_,lvl) -> Subst.set_info_con lvl value s
      | LP.App xs -> aux (L.hd xs)
      | _ -> assert false in aux frozen);
  extern_vv "get-frozen-info" (fun frozen out s ->
    let rec aux frozen =
      match LP.look frozen with
      | LP.Con(_,lvl) ->
          (match Subst.get_info_con lvl s with
          | None -> raise NoClause
          | Some t -> unify t out s)
      | LP.App xs -> aux (L.hd xs)
      | _ -> assert false in aux frozen)
;;

let register_telescope () =
  let bind v t = LP.mapi LP.(fun i t ->
    if equal t v then mkDB i else t) 1 t in
  extern_vv "telescope" LP.(fun ctx value s ->
    let ctx, s = Red.nf ctx s in
    let ctx = check_list "telescope" ctx in
    if ctx = [] then unify mkNil value s else
    let t, binders = List.hd ctx, List.tl ctx in
    let binders = List.map (check_list2 "telescope") binders in
    let tele = List.fold_left (fun t (var,typ) ->
      fixApp (L.of_list [typ;mkBin 1 (bind var t)]))
      t binders in
    unify tele value s)
;;

let _ = Printexc.record_backtrace true
let _ =
  let control = Gc.get () in
  let tweaked_control = { control with
    Gc.minor_heap_size = 33554432; (** 4M *)
    Gc.space_overhead = 120;
  } in
  Gc.set tweaked_control;
  register_print ();
  register_custom_predicate "is_flex" (fun t s ->
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
(*
  register_custom_predicate "zero_level" (fun t s ->
    let h, s = Subst.fresh_uv 0 s in
    protect (unify t h) s);
*)
  let destApp x = LP.(match look x with
    | App xs -> L.hd xs, L.tl xs
    | _ -> x, L.empty) in
  register_custom_control_operator "delayed" (fun t s (g,dls,p)  alts ->
    let keys =
      List.map (fun (t,_,_,_,_) -> fst(destApp (fst(Red.nf t s)))) dls in
    let kl = LP.(mkSeq (L.of_list (Lprun.uniq keys)) mkNil) in
    let s = unify t kl s in
    s, (List.tl g,dls,p), alts);
  let ppgoal s a eh filter =
    let filter = check_list "ppgoal" filter in
    Format.eprintf "@[<hv 0>%a@ |- %a@]"
      (LP.prf_program ~compact:false)
        (List.map (fun (a,b,p,n) -> a,b,fst(Red.nf p s),n)
          (List.filter (fun (_,k,_,_) ->
             match k with
             | LP.Flex -> false
             | LP.Key x ->
                 List.exists (LP.equal x) filter)
             eh))
      (LP.prf_premise []) (fst(Red.nf a s)) in
  let skip (l,d,p) = List.tl l,d,p in
  register_custom_control_operator "pr_delayed" (fun t s (_,d,_ as gls) alts ->
    let t, s = Red.nf t s in
    let t, filter = check_list2 "pr_delayed" t in
    let selected, _ =
      List.partition (fun (k,_,_,_,_) ->
        let k = fst(destApp (fst(Red.nf k s))) in
        LP.equal k t) d in
    match selected with
    | (key,a,depth,eh,lvl) :: _ -> ppgoal s a eh filter; s, skip gls, alts
    | [] -> raise NoClause);
  register_custom_control_operator "schedule" (fun t s (gls,dls,p) alts ->
    let t, s = Red.nf t s in
    let v1, v2 = check_list2 "schedule" t in
    let open LP in
    let resumed, _ =
      List.partition (fun (t,_,_,_,_) ->
        let k = fst(destApp (fst(Red.nf t s))) in
        LP.equal k v1) dls in
    match resumed with
    | (key,a,depth,eh,lvl) :: _ ->
         let gl, s = goals_of_premise p v2 depth eh lvl s in
         let g1, gl = List.hd gl, List.tl gl in
         (match g1 with
         | _,`Atom (k,_),_,_,_ ->
            let s = unify key k s in
            s,(gl @ List.tl gls, dls, p),alts
         | _ -> raise (Invalid_argument "schedule"))
    | [] -> raise NoClause);
  register_frozen_tab ();
  register_telescope ();
  register_custom_control_operator "context" (fun t s (gls,dls,p) alts ->
    let t, s = Red.nf t s in
    let t = check_list1 "context" t in
    let s =
      match gls with
      | (ctx1,_,_,_,_) :: _ ->
           let rec aux = function
             | [] -> []
             | None :: rest -> aux rest
             | Some x :: rest -> x :: aux rest in
           let ctx = LP.(mkSeq (L.of_list (aux ctx1)) mkNil) in
           unify ctx t s
      | _ -> s in
    s, (List.tl gls,dls,p), alts)
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

let parse_argv argv =
  let max_w = ref None in
  let rec aux = function
    | [] -> []
    | "-max-w" :: cols :: rest -> max_w := Some (int_of_string cols); aux rest
    | x :: rest -> x :: aux rest in
  let rest = aux (Array.to_list argv) in
  set_terminal_width ?max_w:!max_w ();
  Array.of_list rest
;;

let _ =
  let argv = Trace.parse_argv Sys.argv in
  let argv = parse_argv argv in
  let b = Buffer.create 1024 in
  for i=1 to Array.length argv - 1 do
    Printf.eprintf "loading %s\n" argv.(i);
      let ic = open_in argv.(i) in
      try
        while true do Buffer.add_string b (input_line ic^"\n") done;
        assert false
      with End_of_file -> ()
  done;
  let p = Buffer.contents b in
  let g =
    Printf.printf "goal> %!";
    input_line stdin in
  test_prog p g;
  Trace.quit ()

