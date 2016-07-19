(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department, University of Bologna, Italy.                     
    ||I||                                                                
    ||T||  HELM is free software; you can redistribute it and/or         
    ||A||  modify it under the terms of the GNU General Public License   
    \   /  version 2 or (at your option) any later version.      
     \ /   This software is distributed as is, NO WARRANTY.     
      V_______________________________________________________________ *)

(* $Id: nCicMetaSubst.ml 12531 2013-02-27 20:19:04Z sacerdot $ *)

let debug = ref false;;
let indent = ref "";;
let times = ref [];;
let pp s =
 if !debug then
  prerr_endline (Printf.sprintf "%-20s" !indent ^ " " ^ Lazy.force s)
;;
let inside c =
 if !debug then
  begin
   let time1 = Unix.gettimeofday () in
   indent := !indent ^ String.make 1 c;
   times := time1 :: !times;
   prerr_endline ("{{{" ^ !indent ^ " ")
  end
;;
let outside exc_opt =
 if !debug then
  begin
   let time2 = Unix.gettimeofday () in
   let time1 =
    match !times with time1::tl -> times := tl; time1 | [] -> assert false in
   prerr_endline ("}}} " ^ string_of_float (time2 -. time1));
   (match exc_opt with
   | Some e ->  prerr_endline ("exception raised: " ^ Printexc.to_string e)
   | None -> ());
   try
    indent := String.sub !indent 0 (String.length !indent -1)
   with
    Invalid_argument _ -> indent := "??"; ()
  end
;;

exception MetaSubstFailure of string Lazy.t
exception Uncertain of string Lazy.t

let newmeta,maxmeta,pushmaxmeta,popmaxmeta = 
  let maxmeta = ref 0 in
  let pushedmetas = ref [] in
  (fun () -> incr maxmeta; !maxmeta),
  (fun () -> !maxmeta),
  (fun () -> pushedmetas := !maxmeta::!pushedmetas; maxmeta := 0),
  (fun () -> match !pushedmetas with [] -> assert false | hd::tl -> pushedmetas := tl)
;;

exception NotFound of [`NotInTheList | `NotWellTyped];;

let position to_skip n (shift, lc) =
  match lc with
  | NCic.Irl len when n <= shift + to_skip || n > shift + len ->
     raise (NotFound `NotInTheList)
  | NCic.Irl _ -> n - shift
  | NCic.Ctx tl ->
      let rec aux to_skip k = function 
         | [] -> raise (NotFound `NotInTheList)
         | _ :: tl when to_skip > 0 -> aux (to_skip - 1) (k+1) tl
         | (NCic.Rel m)::_ when m + shift = n -> k
         | _::tl -> aux to_skip (k+1) tl 
      in
       aux to_skip 1 tl
;;

let pack_lc orig = 
  let rec are_contiguous k = function
    | [] -> true
    | (NCic.Rel j) :: tl when j = k+1 -> are_contiguous j tl
    | _ -> false
  in
  match orig with
  | _, NCic.Ctx [] -> 0, NCic.Irl 0
  | shift, NCic.Ctx (NCic.Rel k::tl as l) when are_contiguous k tl ->
      shift+k-1, NCic.Irl (List.length l)
  | _ -> orig
;;



let mk_perforated_irl shift len restrictions =
  let rec aux n =
    if n = 0 then [] else
     if List.mem (n+shift) restrictions then aux (n-1)
     else (NCic.Rel n) :: aux (n-1)
  in
    pack_lc (shift, NCic.Ctx (List.rev (aux len)))
;;

exception Occur;;

let purge_restricted restrictions more_restrictions l =
 if more_restrictions = [] then l
 else
  begin
   pp (lazy ("TO BE RESTRICTED: " ^ 
    (String.concat "," (List.map string_of_int restrictions))));
   pp (lazy ("MORE RESTRICTIONS: " ^ 
    (String.concat "," (List.map string_of_int more_restrictions))));
   let shift,lc = l in
   let lc = NCicUtils.expand_local_context lc in
    let rec aux n lc =
     match lc with
        [] -> []
      | _ when List.mem n restrictions -> aux (n+1) lc
      | _::tl when List.mem n more_restrictions -> aux (n+1) tl
      | he::tl -> he::aux (n+1) tl
    in
    pack_lc (shift, NCic.Ctx (aux 1 lc))
  end
;;

let rec force_does_not_occur status metasenv subst restrictions t =
 let rec aux k ms = function
    | NCic.Rel r when List.mem (r - k) restrictions -> raise Occur
    | NCic.Rel r as orig ->
        let amount = 
          List.length (List.filter (fun x -> x < r - k) restrictions) 
        in
        if amount > 0 then ms, NCic.Rel (r - amount) else ms, orig
    | NCic.Meta (n, (shift,lc as l)) as orig ->
       (try
         let _,_,bo,_ = NCicUtils.lookup_subst n subst in
          aux k ms (NCicSubstitution.subst_meta status l bo)
        with
         NCicUtils.Subst_not_found _ ->
          (* we ignore the subst since restrict will take care of already
           * instantiated/restricted metavariabels *)
          let l = NCicUtils.expand_local_context lc in
          let sl = List.map (NCicSubstitution.lift status shift) l in 
          let (metasenv,subst as ms), _, restrictions_for_n, l' =
             List.fold_right
               (fun t (ms, i, restrictions_for_n, l) ->
                 try 
              (*pp (lazy ("L'ORLO DELLA FOSSA: k= " ^ string_of_int k ^ " shift=" ^
               string_of_int shift ^ " t=" ^ status#ppterm ~metasenv ~subst ~context:[] t));*)
                   let ms, t = aux k ms t in
              (*pp (lazy ("LA FOSSA: " ^ status#ppterm ~metasenv ~subst ~context:[] t));*)
                   ms, i-1, restrictions_for_n, t::l
                 with Occur ->
                   ms, i-1, i::restrictions_for_n, l)
               sl (ms, List.length l, [], [])
          in
          if restrictions_for_n = [] then
            ms, if sl = l' then orig else (
                (*pp (lazy ("FINITO: " ^ status#ppterm ~metasenv:[] ~subst:[]
                  ~context:[] (NCic.Meta (n,pack_lc (0, NCic.Ctx l')))));*)
              NCic.Meta (n, pack_lc (0, NCic.Ctx l'))
            )
          else
            let l' = pack_lc (0, NCic.Ctx l') in
            let _ = pp (lazy ("restrictions for n are:" ^ String.concat "," (List.map string_of_int restrictions_for_n))) in
            let metasenv, subst, newmeta, more_restricted = 
              restrict status metasenv subst n restrictions_for_n in
            let _ = pp (lazy ("more restricted: " ^String.concat "," (List.map string_of_int more_restricted))) in
            let l' = purge_restricted restrictions more_restricted l' in
              (metasenv, subst), NCic.Meta (newmeta, l'))
    | t -> NCicUntrusted.map_term_fold_a status (fun _ k -> k+1) k aux ms t
 in
   aux 0 (metasenv,subst) t 

and force_does_not_occur_in_context status metasenv subst restrictions = function
  | name, NCic.Decl t as orig ->
      (* pp (lazy ("CCC: hd is" ^ status#ppterm ~metasenv:[] ~subst:[] ~context:[] t ^
      "\nCCC: restrictions are:" ^ String.concat "," (List.map string_of_int restrictions)));*)
      let (metasenv, subst), t' =
        force_does_not_occur status metasenv subst restrictions t in
      metasenv, subst, (if t == t' then orig else (name,NCic.Decl t'))
  | name, NCic.Def (bo, ty) as orig ->
      let (metasenv, subst), bo' =
        force_does_not_occur status metasenv subst restrictions bo in
      let (metasenv, subst), ty' =
        force_does_not_occur status metasenv subst restrictions ty in
      metasenv, subst, 
       (if bo == bo' && ty == ty' then orig else (name, NCic.Def (bo', ty')))

and erase_in_context status metasenv subst pos restrictions = function
  | [] -> metasenv, subst, restrictions, []
  | hd::tl as orig ->
      let metasenv, subst, restricted, tl' = 
        erase_in_context status metasenv subst (pos+1) restrictions tl in
      if List.mem pos restricted then
        metasenv, subst, restricted, tl'
      else
        try
          let metasenv, subst, hd' =
            let delifted_restricted = 
              List.map ((+) ~-pos) (List.filter ((<=) pos) restricted) in
            force_does_not_occur_in_context 
              status metasenv subst delifted_restricted hd
          in
           metasenv, subst, restricted, 
            (if hd' == hd && tl' == tl then orig else (hd' :: tl'))
        with Occur ->
            metasenv, subst, (pos :: restricted), tl'

and restrict status metasenv subst i (restrictions as orig) =
  assert (restrictions <> []);
  try 
    let name, ctx, bo, ty = NCicUtils.lookup_subst i subst in
      try 
        let metasenv, subst, restrictions, newctx = 
          erase_in_context status metasenv subst 1 restrictions ctx in
        let (metasenv, subst), newty =  
          force_does_not_occur status metasenv subst restrictions ty in
        let (metasenv, subst), newbo =  
          force_does_not_occur status metasenv subst restrictions bo in
        let j = newmeta () in
        let subst_entry_j = j, (name, newctx, newbo, newty) in
        let reloc_irl = mk_perforated_irl 0 (List.length ctx) restrictions in
        let subst_entry_i = i, (name, ctx, NCic.Meta (j, reloc_irl), ty) in
        let new_subst = 
          subst_entry_j :: List.map 
            (fun (n,_) as orig -> if i = n then subst_entry_i else orig) subst
        in
        let diff = List.filter (fun x -> not (List.mem x orig)) restrictions in
        metasenv, new_subst, j, diff
      with Occur -> raise (MetaSubstFailure (lazy (Printf.sprintf
            ("Cannot restrict the context of the metavariable ?%d over "^^
            "the hypotheses %s since ?%d is already instantiated "^^
            "with %s and at least one of the hypotheses occurs in "^^
            "the substituted term") i  (String.concat ", " 
            (List.map (fun x -> fst (List.nth ctx (x-1))) restrictions)) i
            (status#ppterm ~metasenv ~subst ~context:ctx bo))))
  with NCicUtils.Subst_not_found _ -> 
    try 
      let name, ctx, ty = NCicUtils.lookup_meta i metasenv in
      try
        let metasenv, subst, restrictions, newctx = 
          erase_in_context status metasenv subst 1 restrictions ctx in
        let (metasenv, subst), newty =  
          force_does_not_occur status metasenv subst restrictions ty in
        let j = newmeta () in
        let metasenv_entry = j, (name, newctx, newty) in
        let reloc_irl = 
          mk_perforated_irl 0 (List.length ctx) restrictions in
        let subst_entry = i, (name, ctx, NCic.Meta (j, reloc_irl), ty) in
         (* pp (lazy ("BBB: dopo1 \n" ^  NCicPp.ppsubst ~metasenv [subst_entry]));
          pp (lazy ("BBB: dopo2 \n" ^  NCicPp.ppsubst ~metasenv (subst_entry::subst)));
          pp (lazy ("BBB: dopo metasenv\n" ^  NCicPp.ppmetasenv ~subst [metasenv_entry]));*)
        let diff = List.filter (fun x -> not (List.mem x orig)) restrictions in
        List.map 
          (fun (n,_) as orig -> if i = n then metasenv_entry else orig) 
          metasenv,
        subst_entry :: subst, j, diff
      with Occur -> raise (MetaSubstFailure (lazy (Printf.sprintf
          ("Cannot restrict the context of the metavariable ?%d "^^
          "over the hypotheses %s since metavariable's type depends "^^
          "on at least one of them") i (String.concat ", " 
          (List.map (fun x -> fst (List.nth ctx (x-1))) restrictions)))))
    with 
    | NCicUtils.Meta_not_found _ -> assert false
;;

let rec is_flexible status context ~subst = function 
  | NCic.Meta (i,lc) ->
       (try 
          let _,_,t,_ = NCicUtils.lookup_subst i subst in
          let t = NCicSubstitution.subst_meta status lc t in
          is_flexible status context ~subst t
        with NCicUtils.Subst_not_found _ -> true)
  | NCic.Appl (NCic.Meta (i,lc) :: args)-> 
      (try 
        let _,_,t,_ = NCicUtils.lookup_subst i subst in
        let t = NCicSubstitution.subst_meta status lc t in
        is_flexible status context ~subst 
          (NCicReduction.head_beta_reduce status ~delta:max_int 
            (NCic.Appl (t :: args)))
      with NCicUtils.Subst_not_found _ -> true)
   (* this is a cheap whd, it only performs zeta-reduction.
    * 
    * it works when the **omissis** disambiguation algorithm
    * is run on `let x := K a b in t`, K is substituted for a 
    * ? and thus in t metavariables have a flexible Rel
    *)
  | NCic.Rel i ->
      (try
         match List.nth context (i-1)
         with 
         | _,NCic.Def (bo,_) ->
               is_flexible status context ~subst
                 (NCicSubstitution.lift status i bo)
         | _ -> false
      with 
      | Failure _ -> 
          prerr_endline (Printf.sprintf "Rel %d inside context:\n%s" i  
            (status#ppcontext ~subst ~metasenv:[] context));
          assert false
      | Invalid_argument _ -> assert false)
  | _ -> false
;;

let is_out_scope = function `OutScope _ -> true | _ -> false;;
let is_out_scope_tag = List.exists is_out_scope;;
let int_of_out_scope_tag tag = 
 match List.filter is_out_scope tag with [`OutScope n] -> n | _ -> assert false
;;


exception Found;;
exception TypeNotGood;;

(* INVARIANT: we suppose that t is not another occurrence of Meta(n,_), 
   otherwise the occur check does not make sense in case of unification
   of ?n with ?n *)
let delift status ~unify metasenv subst context n l t =
  (*D*)  inside 'D'; try let rc =  
  let is_in_scope_meta subst = function
    | NCic.Meta (i,_) ->
        (try 
           let tag, _, _, _ = NCicUtils.lookup_subst i subst in 
            List.mem `InScope tag
        with NCicUtils.Subst_not_found _ -> false)
    | _ -> false
  in
  let contains_in_scope subst t = 
    let rec aux _ () = function
      | NCic.Meta _ as t ->
          if is_in_scope_meta subst t then raise Found
          else ()
      | t -> 
          if is_in_scope_meta subst t then raise Found
          else NCicUtils.fold (fun _ () -> ()) () aux () t
    in
    try aux () () t; false with Found -> true
  in
  let unify_list in_scope = 
    match l with
    | _, NCic.Irl _ -> fun _ _ _ _ _ -> None
    | shift, NCic.Ctx l -> fun metasenv subst context k t ->
       if is_flexible status context ~subst t || contains_in_scope subst t then None else
         let lb = 
           List.map (fun t -> 
            let t = NCicSubstitution.lift status (k+shift) t in
            t, is_flexible status context ~subst t) 
           l 
         in
         HExtlib.list_findopt
          (fun (li,flexible) i ->
            if flexible || i < in_scope then None else
             match unify metasenv subst context li t with
             | Some (metasenv,subst) -> 
                 Some ((metasenv, subst), NCic.Rel (i+1+k))
             | None -> None)
          lb
  in
  let rec aux (context,k,in_scope) (metasenv, subst as ms) t = 
   match unify_list in_scope metasenv subst context k t with
   | Some x -> x
   | None -> 
    match t with 
    | NCic.Rel n as t when n <= k -> ms, t
    | NCic.Rel n -> 
        (try
          match List.nth context (n-1) with
          | _,NCic.Def (bo,_) -> 
                (try ms, NCic.Rel ((position in_scope (n-k) l) + k)
                 with (NotFound `NotInTheList) ->
                (* CSC: This bit of reduction hurts performances since it is
                 * possible to  have an exponential explosion of the size of the
                 * proof. required for nat/nth_prime.ma *)
                  aux (context,k,in_scope) ms (NCicSubstitution.lift status n bo))
          | _,NCic.Decl _ -> ms, NCic.Rel ((position in_scope (n-k) l) + k)
        with Failure _ -> assert false) (*Unbound variable found in delift*)
    | NCic.Meta (i,_) when i=n ->
         raise (MetaSubstFailure (lazy (Printf.sprintf (
           "Cannot unify the metavariable ?%d with a term that has "^^
           "as subterm %s in which the same metavariable "^^
           "occurs (occur check)") i 
            (status#ppterm ~context ~metasenv ~subst t))))
    | NCic.Meta (i,l1) as orig ->
        (try
           let tag,c,t,ty = NCicUtils.lookup_subst i subst in
           let in_scope, clear = 
            if List.mem `InScope tag then 0, true
            else if is_out_scope_tag tag then int_of_out_scope_tag tag,true
            else in_scope, false
           in
           let ms = 
             if not clear then ms
             else 
               metasenv, 
               (i,([],c,t,ty)) :: List.filter (fun j,_ -> i <> j) subst
           in
           aux (context,k,in_scope) ms (NCicSubstitution.subst_meta status l1 t)
         with NCicUtils.Subst_not_found _ ->
           if snd l1 = NCic.Irl 0 || snd l1 = NCic.Ctx [] then ms, orig
           else
              let shift1,lc1 = l1 in
              let shift,lc = l in
              let shift = shift + k in
              match lc, lc1 with
              | NCic.Irl len, NCic.Irl len1 
                when shift1 + len1 < shift || shift1 > shift + len ->
                  let restrictions = HExtlib.list_seq 1 (len1 + 1) in
                  let metasenv, subst, newmeta, more_restricted = 
                   restrict status metasenv subst i restrictions in
                  let l' = (0,NCic.Irl (max 0 (k-shift1))) in
                  let l' = purge_restricted restrictions more_restricted l' in
                  (metasenv, subst),NCic.Meta (newmeta,l')
              | NCic.Irl len, NCic.Irl len1 ->
                  let low_restrictions, new_shift = 
                    if k <= shift1 && shift1 < shift then 
                      HExtlib.list_seq 1 (shift - shift1 + 1), k
                    else if shift1 < k (* <= shift *) then
                      let save_below = k - shift1 in
                      HExtlib.list_seq (save_below + 1) (shift - shift1 + 1),
                      shift1
                    else [], shift1 - shift + k
                  in
                  let high_restrictions = 
                    let last = shift + len in
                    let last1 = shift1 + len1 in
                    if last1 > last then
                      let high_gap = last1 - last in
                      HExtlib.list_seq (len1 - high_gap + 1) (len1 + 1)
                    else []
                  in
                  let restrictions = low_restrictions @ high_restrictions in
                  if restrictions = [] then
                    if shift = k then ms, orig
                    else ms, NCic.Meta (i, (new_shift, lc1))
                  else
                    let metasenv, subst, newmeta, more_restricted = 
                     restrict status metasenv subst i restrictions in
                    let newlc_len = len1 - List.length restrictions in 
                    let l' = new_shift, NCic.Irl newlc_len in
                    let l' = purge_restricted restrictions more_restricted l' in
                    (metasenv, subst),NCic.Meta(newmeta,l')

              | _ ->
                  let lc1 = NCicUtils.expand_local_context lc1 in
                  let lc1 = List.map (NCicSubstitution.lift status shift1) lc1 in
                  let rec deliftl tbr j ms = function
                    | [] -> ms, tbr, []
                    | t::tl ->
                        let ms, tbr, tl = deliftl tbr (j+1) ms tl in
                        try 
                          let ms, t = aux (context,k,in_scope) ms t in 
                          ms, tbr, t::tl
                        with
                        | (NotFound `NotInTheList) | MetaSubstFailure _ -> ms, j::tbr, tl
                  in
                  let (metasenv, subst), to_be_r, lc1' = deliftl [] 1 ms lc1 in
                  pp (lazy ("TO BE RESTRICTED: " ^ 
                   (String.concat "," (List.map string_of_int to_be_r))));
                  let l1 = pack_lc (0, NCic.Ctx lc1') in
                  pp (lazy ("newmeta:" ^ status#ppterm
                   ~metasenv ~subst ~context (NCic.Meta (999,l1))));
                  pp (lazy (status#ppmetasenv ~subst metasenv));
                  if to_be_r = [] then
                    (metasenv, subst), 
                    (if lc1' = lc1 then orig else NCic.Meta (i,l1))
                  else
                    let metasenv, subst, newmeta, more_restricted = 
                     restrict status metasenv subst i to_be_r in
                    let l1 = purge_restricted to_be_r more_restricted l1 in
                     (metasenv, subst), NCic.Meta(newmeta,l1))

    | t -> 
        NCicUntrusted.map_term_fold_a status
          (fun e (c,k,s) -> (e::c,k+1,s)) (context,k,in_scope) aux ms t
  in
(*
  prerr_endline (
    "DELIFTO " ^ status#ppterm ~metasenv ~subst ~context t ^ " w.r.t. " ^
    status#ppterm ~metasenv ~subst ~context (NCic.Meta(n,l)) ^ " i.e. " ^
    String.concat ", " (List.map (status#ppterm ~metasenv ~subst ~context) ( 
      let shift, lc = l in
      (List.map (NCicSubstitution.lift status shift) 
        (NCicUtils.expand_local_context lc))
  )));
*)
   try
(*assert (try n = -1 or (ignore(NCicUtils.lookup_meta n metasenv); true) with NCicUtils.Meta_not_found _ -> false);*)
    let ((metasenv,subst),t) as res = aux (context,0,0) (metasenv,subst) t in
    if (try n <> -1 && (ignore(NCicUtils.lookup_meta n metasenv); false)
        with NCicUtils.Meta_not_found _ -> true)
    then
     let _,context,bo,_ = NCicUtils.lookup_subst n subst in
      match unify metasenv subst context bo t with
         None -> raise (NotFound `NotWellTyped)
       | Some (metasenv,subst) -> (metasenv,subst),t
    else
    (try
      let _,context,ty = NCicUtils.lookup_meta n metasenv in
      let ty' =
       match t with
          NCic.Sort _ -> (* could be algebraic *) NCic.Implicit `Closed
        | _ -> NCicTypeChecker.typeof status ~subst ~metasenv context t in
       (match ty,ty' with
           NCic.Implicit _,_ ->
            (match ty' with
                NCic.Sort _ | NCic.Meta _ | NCic.Implicit _ -> res
              | _ -> raise TypeNotGood)
         | _,NCic.Implicit _ ->
            (match ty with
                NCic.Sort _ | NCic.Meta _ | NCic.Implicit _ -> res
              | _ -> raise TypeNotGood)
         | _ ->
           if
            NCicReduction.are_convertible status ~metasenv ~subst context ty' ty
           then
            res
           else
            raise TypeNotGood)
     with
        NCicUtils.Meta_not_found _ ->
         (* Fake metavariable used in NTacStatus and NCicRefiner :-( *)
         assert (n = -1); res
      | NCicTypeChecker.TypeCheckerFailure msg ->
         HLog.error "----------- Problem with Dependent Types ----------";
         HLog.error (Lazy.force msg) ;
         HLog.error "---------------------------------------------------";
         raise (NotFound `NotWellTyped)
      | TypeNotGood
      | NCicTypeChecker.AssertFailure _
      | NCicReduction.AssertFailure _
      | NCicTypeChecker.TypeCheckerFailure _ ->
         raise (NotFound `NotWellTyped))
   with NotFound reason ->
      (* This is the case where we fail even first order unification. *)
      (* The reason is that our delift function is weaker than first  *)
      (* order (in the sense of alpha-conversion). See comment above  *)
      (* related to the delift function.                              *)
      let reason =
       match reason with
          `NotInTheList -> "some variable cannot be delifted"
        | `NotWellTyped -> "the unifier found is not well typed" in
      let msg = (lazy (Printf.sprintf
        ("Error trying to abstract %s over [%s]: %s")
        (status#ppterm ~metasenv ~subst
        ~context t) (String.concat "; " (List.map (status#ppterm ~metasenv
        ~subst ~context) (let shift, lc = l in List.map (NCicSubstitution.lift
        status shift) (NCicUtils.expand_local_context lc)))) reason))
      in
      let shift, lc = l in
      let lc = NCicUtils.expand_local_context lc in
      let l = List.map (NCicSubstitution.lift status shift) lc in
       if
        List.exists (fun t-> NCicUntrusted.metas_of_term status subst context t <> [])l
       then
        raise (Uncertain msg)
       else
        raise (MetaSubstFailure msg)
 (*D*)  in outside None; rc with exn -> outside (Some exn); raise exn 
;;

let mk_meta ?(attrs=[]) metasenv context ?with_type kind = 
  assert(kind <> `IsSort || context = []);
  let n = newmeta () in
  let ty= match with_type with None-> NCic.Implicit (`Typeof n)| Some x ->x in
  let len = List.length context in
  let attrs = NCicUntrusted.set_kind kind attrs in
  let menv_entry = (n, (attrs, context, ty)) in
  menv_entry :: metasenv, n, NCic.Meta (n, (0,NCic.Irl len)), ty
;;

let extend_meta metasenv n =
 try
  let attrs,cc,ty = NCicUtils.lookup_meta n metasenv in 
  (match ty with 
  | NCic.Implicit (`Typeof _) -> 
      let mk_meta context kind =
        let metasenv, _, ty, _ = mk_meta metasenv context kind in
        (n, (attrs, cc, ty)) :: List.filter (fun x,_ -> x <> n) metasenv, ty
      in
      (match NCicUntrusted.kind_of_meta attrs with
       | `IsSort 
       | `IsType -> mk_meta [] `IsSort
       | `IsTerm -> mk_meta cc `IsType)
  | ty -> metasenv, ty)
 with NCicUtils.Meta_not_found _ -> assert false
;;

let saturate status ?(delta=0) metasenv subst context ty goal_arity =
 assert (goal_arity >= 0);
  let rec aux metasenv = function
   | NCic.Prod (name,s,t) as ty ->
       let metasenv1, _, arg,_ = 
          mk_meta ~attrs:[`Name name] metasenv context ~with_type:s `IsTerm in
       let t, metasenv1, args, pno = 
           aux metasenv1 (NCicSubstitution.subst status arg t) 
       in
       if pno + 1 = goal_arity then
         ty, metasenv, [], goal_arity+1
       else
         t, metasenv1, arg::args, pno+1
   | ty ->
        match NCicReduction.whd status ~subst context ty ~delta with
        | NCic.Prod _ as ty -> aux metasenv ty
        | ty -> ty, metasenv, [], 0
  in
  let res, newmetasenv, arguments, _ = aux metasenv ty in
  res, newmetasenv, arguments
;;
