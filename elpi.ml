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

let _ = Printexc.record_backtrace true
let _ =
  let control = Gc.get () in
  let tweaked_control = { control with
    Gc.minor_heap_size = 33554432; (** 4M *)
    Gc.space_overhead = 120;
  } in
  Gc.set tweaked_control;
  set_terminal_width ();
  register_custom "print" (fun t s _ _ ->
    let unescape s = Str.global_replace (Str.regexp_string "\\n") "\n" s in
    let t = Red.nf s t in
    (match LP.look t with
    | LP.Ext t  when isString t ->
        Format.eprintf "%s%!" (unescape (getString t))
    | _ -> Format.eprintf "%a%!" (LP.prf_data []) t);
    s);
  register_custom "is" (fun t s _ _ ->
    let t = Red.nf s t in
    match LP.look t with
    | LP.App l when L.len l = 3 ->
        if LP.equal (L.get 1 l) (L.get 2 l) then s else raise NoClause
    | _ -> assert false);
  register_custom "is_flex" (fun t s _ _ ->
    let t, s = Red.whd s t in
    match LP.look t with
    | LP.Uv _ -> s
    | LP.App xs ->
        (match LP.look (L.hd xs) with LP.Uv _ -> s | _ -> raise NoClause)
    | _ -> raise NoClause);
  let aborts = ref 0 in
  register_custom "abort" (fun t s _ _ ->
    incr aborts;
    (match LP.look t with
    | LP.Ext t when isString t ->
         if !aborts = int_of_string (getString t) then exit 1 else s
    | _ -> assert false));
  register_custom "parse" (fun t s _ _ ->
    let t, s = Red.whd s t in
    match LP.look t with
    | LP.Seq (l,_) when L.len l = 2 ->
        let hd, s = Red.whd s (L.hd l) in
        (match LP.look hd with
        | LP.Ext x when isString x ->
            let input = getString x in
            (try unify (LP.parse_data input) (L.get 1 l) s
            with
            | UnifFail _ ->
                prerr_endline "parsing in the wrong ctx?";raise NoClause
            | Stream.Error msg -> prerr_endline msg; raise NoClause)
        | _ -> assert false)
    | _ -> assert false);
  register_custom "read" (fun t s _ _ ->
    let input = input_line stdin in
    unify (LP.mkExt (mkString input)) t s);
;;

let test_prog p g =
 let width = Format.pp_get_margin Format.err_formatter () in
 for i = 0 to width - 1 do Format.eprintf "-"; done;
 Format.eprintf "@\n%!";
 try
  let p = LP.parse_program p in
  let g = LP.parse_goal g in
  Format.eprintf "@[<hv2>program:@ %a@]@\n%!" LP.prf_program p;
  let g, s, dgs = run_dls p g in
  Format.eprintf
    "@\n@[<hv2>output:@ %a@]@\n@[<hv2>nf out:@ %a@]@\n@[<hv2>subst:@ %a@]@\n%!"
    (LP.prf_goal []) (Subst.apply_subst_goal s g) 
    (LP.prf_goal []) (LP.map_premise (Red.nf s) g)
    Subst.prf_subst s;
 List.iter (fun g ->
  Format.eprintf
    "@[<hv2>delay:@ %a@]@\n%!"
    (LP.prf_goal []) (LP.map_premise (Red.nf s) g)) dgs

 with Stream.Error msg ->
   Format.eprintf "@[Parse error: %s@]@\n%!" msg
;;

let _ =
  for i=1 to Array.length Sys.argv - 1 do
    Printf.eprintf "running with %s\n" Sys.argv.(i);
    let p =
      let b = Buffer.create 1024 in
      let ic = open_in Sys.argv.(i) in
      try
        while true do Buffer.add_string b (input_line ic^"\n") done;
        assert false
      with End_of_file -> Buffer.contents b in
    let g =
      Printf.printf "goal> %!";
      input_line stdin in
(*    Trace.init ~where:("run",1,1000) ~filter_out:["rdx";"push.*";"epush.*";(*"unif";"bind";"t$";"vj$";*)"rule";"whd";"hv";"premise";"psusp";"skipped"] true; *)
    test_prog p g
  done

