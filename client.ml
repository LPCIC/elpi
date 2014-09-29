open Elpi

open Lpdata
open Lprun

module F = Format

let _ =
  let control = Gc.get () in
  let tweaked_control = { control with
    Gc.minor_heap_size = 33554432; (** 4M *)
    Gc.space_overhead = 120;
  } in
  Gc.set tweaked_control
;;

let _ = Printexc.record_backtrace true

let set_terminal_width ?(max_w=
    let ic, _ as p = Unix.open_process "tput cols" in
    let w = int_of_string (input_line ic) in
    let _ = Unix.close_process p in w) () =
  F.pp_set_margin F.err_formatter max_w;
  F.pp_set_ellipsis_text F.err_formatter "...";
  F.pp_set_max_boxes F.err_formatter 30;
;;

let _ =
  register_std ();
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
    let filter = L.to_list (check_list "ppgoal" filter) in
    F.eprintf "@[<hv 0>%a@ |- %a@]"
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
;;

let test_prog p g =
 let width = F.pp_get_margin F.err_formatter () in
 for i = 0 to width - 1 do F.eprintf "-"; done;
 F.eprintf "@\n%!";
 try
  let p = LP.parse_program p in
  let g = LP.parse_goal g in
  (*F.eprintf "@[<hv2>program:@ %a@]@\n%!" LP.prf_program p;*)
  let rec aux (g,assignments,s,dgs,continuation) =
   (*F.eprintf
     "@\n@[<hv2>output:@ %a@]@\n@[<hv2>nf out:@ %a@]@\n@[<hv2>subst:@ %a@]@\n%!"
     (LP.prf_goal []) (Subst.apply_subst_goal s g) 
     (LP.prf_goal []) (LP.map_premise (Red.nf s) g)
     Subst.prf_subst s;*)
   F.eprintf
     "@\n@[<hv2>input:@ %a@]@\n%!"
     (LP.prf_goal []) (fst(Red.nf g (Subst.empty 0)));
   List.iter (fun x ->
    F.eprintf "@[<hv2>%a@ = %a@]@\n%!"
     (LP.prf_data []) x (LP.prf_data []) (fst(Red.nf x s)))
     assignments;
   List.iter (fun (g,eh) ->
    F.eprintf "delay: @[<hv>%a@ |- %a@]\n%!"
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
   F.eprintf "@[Parse error: %s@]@\n%!" msg
;;

let usage () =
  F.eprintf "\nelpi interpreter usage:\telpi OPTS FILES\n";
  F.eprintf "\t-max-w COLS  overrides the number of columns of the terminal\n\n";;

let parse_argv argv =
  let max_w = ref None in
  let rec aux = function
    | [] -> []
    | "-max-w" :: cols :: rest -> max_w := Some (int_of_string cols); aux rest
    | ("-h" | "--help") :: _ -> usage(); exit 1
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

