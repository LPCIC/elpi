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

(* $Id: index.mli 9822 2009-06-03 15:37:06Z tassi $ *)

module Superposition (B : Orderings.Blob) = 
  struct
    module IDX = Index.Index(B)
    module Unif = FoUnif.Founif(B)
    module Subst = FoSubst 
    module Order = B
    module Utils = FoUtils.Utils(B)
    module Pp = Pp.Pp(B)
    
    exception Success of 
      B.t Terms.bag 
      * int 
      * B.t Terms.unit_clause
      * B.t Terms.substitution

    let print s = prerr_endline (Lazy.force s);; 
    let debug _ = ();; 
    let enable = true;;

    let rec list_first f = function
      | [] -> None
      | x::tl -> match f x with Some _ as x -> x | _ -> list_first f tl
    ;;

    let first_position pos ctx t f =
      let inject_pos pos ctx = function
        | None -> None
        | Some (a,b,c,d) -> Some(ctx a,b,c,d,pos)
      in
      let rec aux pos ctx = function
      | Terms.Leaf _ as t -> inject_pos pos ctx (f t)
      | Terms.Var _ -> None
      | Terms.Node l as t->
          match f t with
          | Some _ as x -> inject_pos pos ctx x
          | None ->
              let rec first pre post = function
                | [] -> None
                | t :: tl -> 
                     let newctx = fun x -> ctx (Terms.Node (pre@[x]@post)) in
                     match aux (List.length pre :: pos) newctx t with
                     | Some _ as x -> x
                     | None -> 
                         if post = [] then None (* tl is also empty *)
                         else first (pre @ [t]) (List.tl post) tl
              in
                first [] (List.tl l) l 
      in
        aux pos ctx t
    ;;
                                     
    let all_positions pos ctx t f =
      let rec aux pos ctx = function
      | Terms.Leaf _ as t -> f t pos ctx 
      | Terms.Var _ -> []
      | Terms.Node l as t-> 
          let acc, _, _ = 
            List.fold_left
            (fun (acc,pre,post) t -> (* Invariant: pre @ [t] @ post = l *)
                let newctx = fun x -> ctx (Terms.Node (pre@[x]@post)) in
                let acc = aux (List.length pre :: pos) newctx t @ acc in
                if post = [] then acc, l, []
                else acc, pre @ [t], List.tl post)
             (f t pos ctx, [], List.tl l) l
          in
           acc
      in
        aux pos ctx t
    ;;

    let parallel_positions bag pos ctx id t f =
      let rec aux bag pos ctx id = function
      | Terms.Leaf _ as t -> f bag t pos ctx id
      | Terms.Var _ as t -> bag,t,id
      | Terms.Node (hd::l) as t->
          let bag,t,id1 = f bag t pos ctx id in
            if id = id1 then
              let bag, l, _, id = 
                List.fold_left
                  (fun (bag,pre,post,id) t ->
                     let newctx = fun x -> ctx (Terms.Node (pre@[x]@post)) in
                     let newpos = (List.length pre)::pos in
                     let bag,newt,id = aux bag newpos newctx id t in
                       if post = [] then bag, pre@[newt], [], id
                       else bag, pre @ [newt], List.tl post, id)
                  (bag, [hd], List.tl l, id) l
              in
                bag, Terms.Node l, id
            else bag,t,id1 
            (* else aux bag pos ctx id1 t *) 
      | _ -> assert false
      in
        aux bag pos ctx id t
    ;;

    let visit bag pos ctx id t f =
      let rec aux bag pos ctx id subst = function
      | Terms.Leaf _ as t -> 
	  let  bag,subst,t,id = f bag t pos ctx id in
           assert (subst=[]); bag,t,id
      | Terms.Var i as t ->  
	  let t= Subst.apply_subst subst t in
	    bag,t,id
      | Terms.Node (hd::l) ->
          let bag, l, _, id = 
            List.fold_left
              (fun (bag,pre,post,id) t ->
                 let newctx = fun x -> ctx (Terms.Node (pre@[x]@post)) in
                 let newpos = (List.length pre)::pos in
                 let bag,newt,id = aux bag newpos newctx id subst t in
                   if post = [] then bag, pre@[newt], [], id
                   else bag, pre @ [newt], List.tl post, id)
              (bag, [hd], List.map (Subst.apply_subst subst) (List.tl l), id) l
          in
	  let bag,subst,t,id1 = f bag (Terms.Node l) pos ctx id
	  in
	    if id1 = id then (assert (subst=[]); bag,t,id)
	    else aux bag pos ctx id1 subst t
      | _ -> assert false
      in
        aux bag pos ctx id [] t
    ;;
    
    let build_clause bag filter rule t subst id id2 pos dir =
      let proof = Terms.Step(rule,id,id2,dir,pos,subst) in
      let t = Subst.apply_subst subst t in
      if filter subst then
        let literal = 
          match t with
          | Terms.Node [ Terms.Leaf eq ; ty; l; r ] when B.eq B.eqP eq ->
               let o = Order.compare_terms l r in
               (* CSC: to avoid equations of the form ? -> T that
                  can always be applied and that lead to type-checking errors *)
               (match l,r,o with 
(*
                   (Terms.Var _ | Terms.Node (Terms.Var _ ::_)),_,Terms.Gt
                 | _,(Terms.Var _ | Terms.Node (Terms.Var _ ::_)),Terms.Lt -> assert false
*)
                 | (Terms.Var _ | Terms.Node (Terms.Var _ ::_)),_,(Terms.Incomparable | Terms.Invertible) ->
                    Terms.Equation (l, r, ty, Terms.Lt)
                 | _, (Terms.Var _ | Terms.Node (Terms.Var _ ::_)),(Terms.Incomparable | Terms.Invertible) ->
                    Terms.Equation (l, r, ty, Terms.Gt)
                 | _ -> Terms.Equation (l, r, ty, o))
          | t -> Terms.Predicate t
        in
        let bag, uc = 
          Terms.add_to_bag (0, literal, Terms.vars_of_term t, proof) bag
        in
        Some (bag, uc)
      else
        ((*prerr_endline ("Filtering: " ^ Pp.pp_foterm t);*)None)
    ;;
    let prof_build_clause = HExtlib.profile ~enable "build_clause";;
    let build_clause bag filter rule t subst id id2 pos x =
      prof_build_clause.HExtlib.profile (build_clause bag filter rule t subst id id2 pos) x
    ;;
      
    
    (* ============ simplification ================= *)
    let prof_demod_u = HExtlib.profile ~enable "demod.unify";;
    let prof_demod_r = HExtlib.profile ~enable "demod.retrieve_generalizations";;
    let prof_demod_o = HExtlib.profile ~enable "demod.compare_terms";;
    let prof_demod_s = HExtlib.profile ~enable "demod.apply_subst";;

    let demod table varlist subterm =
      let cands = 
        prof_demod_r.HExtlib.profile 
         (IDX.DT.retrieve_generalizations table) subterm 
      in
      list_first
        (fun (dir, (id,lit,vl,_)) ->
           match lit with
           | Terms.Predicate _ -> assert false
           | Terms.Equation (l,r,_,o) ->
               let side, newside = if dir=Terms.Left2Right then l,r else r,l in
               try 
                 let subst =
                   prof_demod_u.HExtlib.profile 
                     (Unif.unification (* (varlist@vl) *) varlist subterm) side 
                 in 
                 let side = 
                   prof_demod_s.HExtlib.profile 
                     (Subst.apply_subst subst) side 
                 in
                 let newside = 
                   prof_demod_s.HExtlib.profile 
                     (Subst.apply_subst subst) newside 
                 in
                 if o = Terms.Incomparable || o = Terms.Invertible then
                   let o = 
                     prof_demod_o.HExtlib.profile 
                      (Order.compare_terms newside) side in
                   (* Riazanov, pp. 45 (ii) *)
                   if o = Terms.Lt then
                     Some (newside, subst, id, dir)
                   else 
                     ((*prerr_endline ("Filtering: " ^ 
                        Pp.pp_foterm side ^ " =(< || =)" ^ 
                        Pp.pp_foterm newside ^ " coming from " ^ 
                        Pp.pp_unit_clause uc );*)None)
                 else
                   Some (newside, subst, id, dir)
               with FoUnif.UnificationFailure _ -> None)
        (IDX.ClauseSet.elements cands)
    ;;
    let prof_demod = HExtlib.profile ~enable "demod";;
    let demod table varlist x =
      prof_demod.HExtlib.profile (demod table varlist) x
    ;;

    let mydemod table varlist subterm = 
      let cands = 
        prof_demod_r.HExtlib.profile 
         (IDX.DT.retrieve_generalizations table) subterm 
      in
      list_first
        (fun (dir, ((id,lit,vl,_) as c)) ->
	   debug (lazy("candidate: " 
		       ^ Pp.pp_unit_clause c)); 
           match lit with
           | Terms.Predicate _ -> assert false
           | Terms.Equation (l,r,_,o) ->
               let side, newside = if dir=Terms.Left2Right then l,r else r,l in
               try 
                 let subst =
                   prof_demod_u.HExtlib.profile 
                     (Unif.unification (* (varlist@vl) *) varlist subterm) side 
                 in 
                 let iside = 
                   prof_demod_s.HExtlib.profile 
                     (Subst.apply_subst subst) side 
                 in
                 let inewside = 
                   prof_demod_s.HExtlib.profile 
                     (Subst.apply_subst subst) newside 
                 in
                 if o = Terms.Incomparable || o = Terms.Invertible then
                   let o = 
                     prof_demod_o.HExtlib.profile 
                      (Order.compare_terms inewside) iside in
                   (* Riazanov, pp. 45 (ii) *)
                   if o = Terms.Lt then
                     Some (newside, subst, id, dir)
                   else 
                     ((*prerr_endline ("Filtering: " ^ 
                        Pp.pp_foterm side ^ " =(< || =)" ^ 
                        Pp.pp_foterm newside ^ " coming from " ^ 
                        Pp.pp_unit_clause uc );*)
		       debug (lazy "not applied");None)
                 else
                   Some (newside, subst, id, dir)
               with FoUnif.UnificationFailure _ -> 
                 debug (lazy "not applied"); None)
        (IDX.ClauseSet.elements cands)
    ;;

    let ctx_demod table vl bag t pos ctx id =
      match mydemod table vl t with
        | None -> (bag,[],t,id)
        | Some (newside, subst, id2, dir) ->
	    let inewside = Subst.apply_subst subst newside in
            match build_clause bag (fun _ -> true)
              Terms.Demodulation (ctx inewside) subst id id2 pos dir
            with
              | None -> assert false
              | Some (bag,(id,_,_,_)) ->
                    (bag,subst,newside,id)
    ;;
      
    let rec demodulate bag (id, literal, vl, pr) table =
      debug (lazy ("demodulate " ^ (string_of_int id)));
       match literal with
      | Terms.Predicate t -> (* assert false *)
	  let bag,_,id1 =
	    visit bag [] (fun x -> x) id t (ctx_demod table vl)
	  in          
	  let cl,_,_ = Terms.get_from_bag id1 bag in
	    bag,cl
      | Terms.Equation (l,r,ty,_) ->
          let bag,l,id1 = 
	    visit bag [2]
            (fun x -> Terms.Node [ Terms.Leaf B.eqP; ty; x; r ]) id l
            (ctx_demod table vl)
	  in 
	  let bag,_,id2 = 
            visit bag [3]
              (fun x -> Terms.Node [ Terms.Leaf B.eqP; ty; l; x ]) id1 r
              (ctx_demod table vl)
	  in 
          let cl,_,_ = Terms.get_from_bag id2 bag in
	    bag,cl
    ;;
      
    let parallel_demod table vl bag t pos ctx id =
      match demod table vl t with
        | None -> (bag,t,id)
        | Some (newside, subst, id2, dir) ->
            match build_clause bag (fun _ -> true)
              Terms.Demodulation (ctx newside) subst id id2 pos dir
            with
              | None -> assert false
              | Some (bag,(id,_,_,_)) ->
                    (bag,newside,id)
    ;;

    let are_alpha_eq cl1 cl2 =
      let get_term (_,lit,_,_) =
        match lit with
          | Terms.Predicate _ -> assert false
          | Terms.Equation (l,r,ty,_) ->
              Terms.Node [Terms.Leaf B.eqP; ty; l ; r]
      in
        try ignore(Unif.alpha_eq (get_term cl1) (get_term cl2)) ; true
        with FoUnif.UnificationFailure _ -> false
    ;;

    let prof_demodulate = HExtlib.profile ~enable "demodulate";;
    let demodulate bag clause x =
      prof_demodulate.HExtlib.profile (demodulate bag clause) x
    ;;

    (* move away *)
    let is_identity_clause = function
      | _, Terms.Equation (_,_,_,Terms.Eq), _, _ -> true
      | _, Terms.Equation (_,_,_,_), _, _ -> false
      | _, Terms.Predicate _, _, _ -> assert false          
    ;;

    let is_identity_goal = function
      | _, Terms.Equation (_,_,_,Terms.Eq), _, _ -> Some []
      | _, Terms.Equation (l,r,_,_), vl, proof ->
          (try Some (Unif.unification (* vl *) [] l r)
           with FoUnif.UnificationFailure _ -> None)
      | _, Terms.Predicate _, _, _ -> assert false          
    ;;

    let build_new_clause_reloc bag maxvar filter rule t subst id id2 pos dir =
      let maxvar, _vl, subst = Utils.relocate maxvar (Terms.vars_of_term
      (Subst.apply_subst subst t)) subst in
      match build_clause bag filter rule t subst id id2 pos dir with
      | Some (bag, c) -> Some ((bag, maxvar), c), subst
      | None -> None,subst
    ;;

    let build_new_clause bag maxvar filter rule t subst id id2 pos dir =
      fst (build_new_clause_reloc bag maxvar filter rule t 
	     subst id id2 pos dir)
    ;;

    let prof_build_new_clause = HExtlib.profile ~enable "build_new_clause";;
    let build_new_clause bag maxvar filter rule t subst id id2 pos x =
      prof_build_new_clause.HExtlib.profile (build_new_clause bag maxvar filter
      rule t subst id id2 pos) x
    ;;

    let fold_build_new_clause bag maxvar id rule filter res =
      let (bag, maxvar), res =
       HExtlib.filter_map_acc 
         (fun (bag, maxvar) (t,subst,id2,pos,dir) ->
            build_new_clause bag maxvar filter rule t subst id id2 pos dir)
         (bag, maxvar) res
      in
       bag, maxvar, res
    ;;
    
    (* rewrite_eq check if in table there an equation matching l=r; 
       used in subsumption and deep_eq. In deep_eq, we need to match 
       several times times w.r.t. the same table, hence we should refresh 
       the retrieved clauses, to avoid clashes of variables *)

    let rewrite_eq ~refresh ~unify maxvar l r ty vl table =
      let retrieve = if unify then IDX.DT.retrieve_unifiables
      else IDX.DT.retrieve_generalizations in
      let lcands = retrieve table l in
      let rcands = retrieve table r in
      let f b c =
        let id, dir, l, r, vl = 
          match c with
            | (d, (id,Terms.Equation (l,r,ty,_),vl,_))-> id, d, l, r, vl
            |_ -> assert false 
        in 
        let reverse = (dir = Terms.Left2Right) = b in
        let l, r, proof_rewrite_dir = if reverse then l,r,Terms.Left2Right
        else r,l, Terms.Right2Left in
          (id,proof_rewrite_dir,Terms.Node [ Terms.Leaf B.eqP; ty; l; r ], vl)
      in
      let cands1 = List.map (f true) (IDX.ClauseSet.elements lcands) in
      let cands2 = List.map (f false) (IDX.ClauseSet.elements rcands) in
      let t = Terms.Node [ Terms.Leaf B.eqP; ty; l; r ] in
      let locked_vars = if unify then [] else vl in
      let rec aux = function
        | [] -> None
        | (id2,dir,c,vl1)::tl ->
            try
              let c,maxvar = if refresh then
                let maxvar,_,r = Utils.relocate maxvar vl1 [] in
                Subst.apply_subst r c,maxvar
                else c,maxvar in 
              let subst = Unif.unification (* (vl@vl1) *) locked_vars c t in
              Some (id2, dir, subst, maxvar)
            with FoUnif.UnificationFailure _ -> aux tl
      in
        aux (cands1 @ cands2)
    ;;

    let is_subsumed ~unify bag maxvar (id, lit, vl, _) table =
      match lit with
      | Terms.Predicate _ -> assert false
      | Terms.Equation (l,r,ty,_) -> 
          match rewrite_eq ~refresh:false ~unify maxvar l r ty vl table with
            | None -> None
            | Some (id2, dir, subst, maxvar) ->
                let id_t = Terms.Node [ Terms.Leaf B.eqP; ty; r; r ] in
                  build_new_clause bag maxvar (fun _ -> true)
                  Terms.Superposition id_t subst id id2 [2] dir 
    ;;
    let prof_is_subsumed = HExtlib.profile ~enable "is_subsumed";;
    let is_subsumed ~unify bag maxvar c x =
      prof_is_subsumed.HExtlib.profile (is_subsumed ~unify bag maxvar c) x
    ;;
    (* id refers to a clause proving contextl l = contextr r *)

    let rec deep_eq ~unify l r ty pos contextl contextr table acc =
      (* let _ = prerr_endline ("pos = " ^ String.concat "," 
            (List.map string_of_int pos)) in *)
      match acc with 
      | None -> None
      | Some(bag,maxvar,(id,lit,vl,p),subst) -> 
          (* prerr_endline ("input subst = "^Pp.pp_substitution subst); *)
          (* prerr_endline ("l prima =" ^ Pp.pp_foterm l); *)
          (* prerr_endline ("r prima =" ^ Pp.pp_foterm r); *)
          let l = Subst.apply_subst subst l in 
          let r = Subst.apply_subst subst r in 
          (* prerr_endline ("l dopo =" ^ Pp.pp_foterm l); *)
          (* prerr_endline ("r dopo =" ^ Pp.pp_foterm r); *)
            try 
              let subst1 = Unif.unification (* vl *) [] l r in
              let lit = 
                match lit with Terms.Predicate _ -> assert false
                  | Terms.Equation (l,r,ty,o) -> 
                    let l = Subst.apply_subst subst1 l in 
                    let r = Subst.apply_subst subst1 r in 
                     Terms.Equation (l, r, ty, o)
              in
                Some(bag,maxvar,(id,lit,vl,p),Subst.concat subst1 subst)
            with FoUnif.UnificationFailure _ -> 
              match rewrite_eq ~refresh:true ~unify maxvar l r ty vl table with
              | Some (id2, dir, subst1, maxvar) ->
		  (* prerr_endline ("subst1 = "^Pp.pp_substitution subst1);
		    prerr_endline ("old subst = "^Pp.pp_substitution subst); *)
                  let newsubst = Subst.concat subst1 subst in
                  let id_t = 
                    FoSubst.apply_subst newsubst
                      (Terms.Node[Terms.Leaf B.eqP;ty;contextl r;contextr r]) 
                  in
                  (match 
                      build_new_clause_reloc bag maxvar (fun _ -> true)
                        Terms.Superposition id_t 
                        subst1 id id2 (pos@[2]) dir  
                   with
                    | Some ((bag, maxvar), c), r ->
                     (* prerr_endline ("creo "^ Pp.pp_unit_clause c); *)
                     (* prerr_endline ("r = "^Pp.pp_substitution r); *)
			let newsubst = Subst.flat 
			  (Subst.concat r subst) in
                        Some(bag,maxvar,c,newsubst)
                    | None, _ -> assert false)
              | None ->
                  match l,r with 
                  | Terms.Node (a::la), Terms.Node (b::lb) when 
                      a = b && List.length la = List.length lb ->
                      let acc,_,_,_ =
                        List.fold_left2 
                          (fun (acc,pre,postl,postr) a b -> 
                             let newcl = 
                              fun x -> contextl(Terms.Node (pre@(x::postl))) in
                             let newcr = 
                              fun x -> contextr(Terms.Node (pre@(x::postr))) in
                             let newpos = List.length pre::pos in
                             let footail l =
                               if l = [] then [] else List.tl l in
                               (deep_eq ~unify a b ty 
                                 newpos newcl newcr table acc,pre@[b],
                                 footail postl, footail postr))
                          (acc,[a],List.tl la,List.tl lb) la lb
                      in acc
                  | _,_ -> None
    ;;

    let prof_deep_eq = HExtlib.profile ~enable "deep_eq";;
    let deep_eq ~unify l r ty pos contextl contextr table x =
      prof_deep_eq.HExtlib.profile (deep_eq ~unify l r ty pos contextl contextr table) x
    ;;

    let rec orphan_murder bag acc i =
      match Terms.get_from_bag i bag with
        | (_,_,_,Terms.Exact _),discarded,_ -> (discarded,acc)
        | (_,_,_,Terms.Step (_,i1,i2,_,_,_)),true,_ -> (true,acc)
        | (_,_,_,Terms.Step (_,i1,i2,_,_,_)),false,_ ->
            if (List.mem i acc) then (false,acc)
            else match orphan_murder bag acc i1 with
              | (true,acc) -> (true,acc)
              | (false,acc) ->
                  let (res,acc) = orphan_murder bag acc i2 in
                  if res then res,acc else res,i::acc
    ;;

    let orphan_murder bag actives cl =
      let (id,_,_,_) = cl in
      let actives = List.map (fun (i,_,_,_) -> i) actives in
      let (res,_) = orphan_murder bag actives id in
        if res then debug (lazy "Orphan murdered"); res
    ;;
    let prof_orphan_murder = HExtlib.profile ~enable "orphan_murder";;
    let orphan_murder bag actives x =
      prof_orphan_murder.HExtlib.profile (orphan_murder bag actives) x
    ;;

    (* demodulate and check for subsumption *)
    let simplify table maxvar bag clause =
      debug (lazy "simplify...");
      if is_identity_clause clause then bag,None
      (* else if orphan_murder bag actives clause then bag,None *)
      else let bag, clause = demodulate bag clause table in
      if is_identity_clause clause then bag,None
      else
        match is_subsumed ~unify:false bag maxvar clause table with
          | None -> bag, Some clause
          | Some _ -> bag, None
    ;;

    let simplify table maxvar bag clause =
      match simplify table maxvar bag clause with
        | bag, None ->
            let (id,_,_,_) = clause in
            let (_,_,iter) = Terms.get_from_bag id bag in
            Terms.replace_in_bag (clause,true,iter) bag, None
        | bag, Some clause -> bag, Some clause
    (*let (id,_,_,_) = clause in
            if orphan_murder bag clause then
              Terms.M.add id (clause,true) bag, Some clause
            else bag, Some clause*)
    ;;
    let prof_simplify = HExtlib.profile ~enable "simplify";;
    let simplify table maxvar bag x =
      prof_simplify.HExtlib.profile (simplify table maxvar bag ) x
    ;;

    let one_pass_simplification new_clause (alist,atable) bag maxvar =
      match simplify atable maxvar bag new_clause with
        | bag,None -> bag,None (* new_clause has been discarded *)
        | bag,(Some clause) ->
            let ctable = IDX.index_unit_clause IDX.DT.empty clause in
            let bag, alist, atable = 
              List.fold_left 
                (fun (bag, alist, atable) c ->
                   match simplify ctable maxvar bag c with
                     |bag,None -> (bag,alist,atable)
                        (* an active clause as been discarded *)
                     |bag,Some c1 ->
                        bag, c :: alist, IDX.index_unit_clause atable c)
                (bag,[],IDX.DT.empty) alist
            in
              bag, Some (clause, (alist,atable))
    ;;
    let prof_one_pass_simplification = HExtlib.profile ~enable "one_pass_simplification";;
    let one_pass_simplification new_clause t bag x =
      prof_one_pass_simplification.HExtlib.profile (one_pass_simplification new_clause t bag ) x
    ;;

    let simplification_step ~new_cl cl (alist,atable) bag maxvar new_clause =
      let atable1 =
        if new_cl then atable else
        IDX.index_unit_clause atable cl
      in
        (* Simplification of new_clause with :      *
         * - actives and cl if new_clause is not cl *
         * - only actives otherwise                 *)
        match
          simplify atable1 maxvar bag new_clause with
          | bag,None -> bag,(Some cl, None) (* new_clause has been discarded *)
          | bag,Some clause ->
              (* Simplification of each active clause with clause *
               * which is the simplified form of new_clause       *)
              let ctable = IDX.index_unit_clause IDX.DT.empty clause in
              let bag, newa, alist, atable = 
                List.fold_left 
                  (fun (bag, newa, alist, atable) c ->
                     match simplify ctable maxvar bag c with
                       |bag,None -> (bag, newa, alist, atable)
                          (* an active clause as been discarded *)
                       |bag,Some c1 ->
                            if (c1 == c) then 
                              bag, newa, c :: alist,
                            IDX.index_unit_clause atable c
                            else
                              bag, c1 :: newa, alist, atable)                  
                  (bag,[],[],IDX.DT.empty) alist
              in
                if new_cl then
                  bag, (Some cl, Some (clause, (alist,atable), newa))
                else
                  (* if new_clause is not cl, we simplify cl with clause *)
                  match simplify ctable maxvar bag cl with
                    | bag,None ->
                        (* cl has been discarded *)
                        bag,(None, Some (clause, (alist,atable), newa))
                    | bag,Some cl1 ->
                        bag,(Some cl1, Some (clause, (alist,atable), newa))
    ;;
    let prof_simplification_step = HExtlib.profile ~enable "simplification_step";;
    let simplification_step ~new_cl cl (alist,atable) bag maxvar x =
      prof_simplification_step.HExtlib.profile (simplification_step ~new_cl cl (alist,atable) bag maxvar) x
    ;;

    let keep_simplified cl (alist,atable) bag maxvar =
      let rec keep_simplified_aux ~new_cl cl (alist,atable) bag newc =
        if new_cl then
          match simplification_step ~new_cl cl (alist,atable) bag maxvar cl with
            | _,(None, _) -> assert false
            | bag,(Some _, None) -> bag,None
            | bag,(Some _, Some (clause, (alist,atable), newa)) ->
                keep_simplified_aux ~new_cl:(cl!=clause) clause (alist,atable)
                  bag (newa@newc)
        else
          match newc with
            | [] -> bag, Some (cl, (alist,atable))
            | hd::tl ->
                match simplification_step ~new_cl cl
                  (alist,atable) bag maxvar hd with
                  | _,(None,None) -> assert false
                  | bag,(Some _,None) ->
                      keep_simplified_aux ~new_cl cl (alist,atable) bag tl
                  | bag,(None, Some _) -> bag,None
                  | bag,(Some cl1, Some (clause, (alist,atable), newa)) ->
                      let alist,atable =
                     (clause::alist, IDX.index_unit_clause atable clause)
                      in
                        keep_simplified_aux ~new_cl:(cl!=cl1) cl1 (alist,atable)
                          bag (newa@tl)
      in
        keep_simplified_aux ~new_cl:true cl (alist,atable) bag []
    ;;
    let prof_keep_simplified = HExtlib.profile ~enable "keep_simplified";;
    let keep_simplified cl t bag x =
      prof_keep_simplified.HExtlib.profile (keep_simplified cl t bag) x
    ;;

    (* this is like simplify but raises Success *)
    let simplify_goal ~no_demod maxvar table bag g_actives clause = 
      let bag, clause = 
        if no_demod then bag, clause else demodulate bag clause table 
      in
      let _ = debug(lazy ("demodulated goal  : " 
			     ^ Pp.pp_unit_clause clause))
      in
      if List.exists (are_alpha_eq clause) g_actives then None
      else match (is_identity_goal clause) with
	| Some subst -> raise (Success (bag,maxvar,clause,subst))
	| None ->
        let (id,lit,vl,_) = clause in 
        (* this optimization makes sense only if we demodulated, since in 
	   that case the clause should have been turned into an identity *)
        if (vl = [] && not(no_demod)) 
	then Some (bag,clause)
        else
         let l,r,ty = 
           match lit with
             | Terms.Equation(l,r,ty,_) -> l,r,ty
             | _ -> assert false 
         in
         match deep_eq ~unify:true l r ty [] (fun x -> x) (fun x -> x) 
           table (Some(bag,maxvar,clause,Subst.id_subst)) with
         | None -> Some (bag,clause)
         | Some (bag,maxvar,cl,subst) -> 
             debug (lazy "Goal subsumed");
             debug (lazy ("subst in superpos: " ^ Pp.pp_substitution subst));
             raise (Success (bag,maxvar,cl,subst))
(*
        match is_subsumed ~unify:true bag maxvar clause table with
        | None -> Some (bag, clause)
        | Some ((bag,maxvar),c) -> 
            debug (lazy "Goal subsumed");
            raise (Success (bag,maxvar,c))
*)
    ;;

    let prof_simplify_goal = HExtlib.profile ~enable "simplify_goal";;
    let  simplify_goal ~no_demod maxvar table bag g_actives x =
      prof_simplify_goal.HExtlib.profile ( simplify_goal ~no_demod maxvar table bag g_actives) x
    ;;

    (* =================== inference ===================== *)

    (* this is OK for both the sup_left and sup_right inference steps *)
    let superposition table varlist subterm pos context =
      let cands = IDX.DT.retrieve_unifiables table subterm in
      HExtlib.filter_map
        (fun (dir, (id,lit,vl,_ (*as uc*))) ->
           match lit with
           | Terms.Predicate _ -> assert false
           | Terms.Equation (l,r,_,o) ->
               let side, newside = if dir=Terms.Left2Right then l,r else r,l in
               try 
                 let subst = 
                   Unif.unification (* (varlist@vl)*)  [] subterm side 
                 in 
                 if o = Terms.Incomparable || o = Terms.Invertible then
                   let side = Subst.apply_subst subst side in
                   let newside = Subst.apply_subst subst newside in
                   let o = Order.compare_terms side newside in
                   (* XXX: check Riazanov p. 33 (iii) *)
                   if o <> Terms.Lt && o <> Terms.Eq then  
                     Some (context newside, subst, id, pos, dir)
                   else 
                     ((*prerr_endline ("Filtering: " ^ 
                        Pp.pp_foterm side ^ " =(< || =)" ^ 
                        Pp.pp_foterm newside);*)None)
                 else
                   Some (context newside, subst, id, pos, dir)
               with FoUnif.UnificationFailure _ -> None)
        (IDX.ClauseSet.elements cands)
    ;;

    (* Superposes selected equation with equalities in table *)
    let superposition_with_table bag maxvar (id,selected,vl,_) table =
      match selected with 
      | Terms.Predicate _ -> assert false
      | Terms.Equation (l,r,ty,Terms.Lt) ->
          fold_build_new_clause bag maxvar id Terms.Superposition
            (fun _ -> true)
            (all_positions [3] 
              (fun x -> Terms.Node [ Terms.Leaf B.eqP; ty; l; x ])
              r (superposition table vl))
      | Terms.Equation (l,r,ty,Terms.Invertible)
      | Terms.Equation (l,r,ty,Terms.Gt) ->
          fold_build_new_clause bag maxvar id Terms.Superposition
            (fun _ -> true)
            (all_positions [2] 
              (fun x -> Terms.Node [ Terms.Leaf B.eqP; ty; x; r ])
              l (superposition table vl))
      | Terms.Equation (l,r,ty,Terms.Incomparable) ->
	  let filtering avoid subst = (* Riazanov: p.33 condition (iv) *)
	    let l = Subst.apply_subst subst l in
	    let r = Subst.apply_subst subst r in
	    let o = Order.compare_terms l r in
	    o <> avoid && o <> Terms.Eq
	  in
          let bag, maxvar,r_terms =
	    fold_build_new_clause bag maxvar id Terms.Superposition
              (filtering Terms.Gt)
              (all_positions [3] 
		 (fun x -> Terms.Node [ Terms.Leaf B.eqP; ty; l; x ])
		 r (superposition table vl))
	  in
	  let bag, maxvar, l_terms =
	    fold_build_new_clause bag maxvar id Terms.Superposition
              (filtering Terms.Lt)
              (all_positions [2] 
		 (fun x -> Terms.Node [ Terms.Leaf B.eqP; ty; x; r ])
		 l (superposition table vl))
	  in
	    bag, maxvar, r_terms @ l_terms
      | _ -> assert false
    ;;

    (* the current equation is normal w.r.t. demodulation with atable
     * (and is not the identity) *)
    let infer_right bag maxvar current (alist,atable) = 
      (* We demodulate actives clause with current until all *
       * active clauses are reduced w.r.t each other         *)
      (* let bag, (alist,atable) = keep_simplified (alist,atable) bag [current] in *)
      let ctable = IDX.index_unit_clause IDX.DT.empty current in
      (* let bag, (alist, atable) = 
        let bag, alist = 
          HExtlib.filter_map_acc (simplify ctable) bag alist
        in
        bag, (alist, List.fold_left IDX.index_unit_clause IDX.DT.empty alist)
      in*)
        debug (lazy "Simplified active clauses with fact");
      (* We superpose active clauses with current *)
      let bag, maxvar, new_clauses =
        List.fold_left 
          (fun (bag, maxvar, acc) active ->
             let bag, maxvar, newc = 
               superposition_with_table bag maxvar active ctable 
             in
             bag, maxvar, newc @ acc)
          (bag, maxvar, []) alist
      in
        debug
	(lazy 
	 ("New clauses :" ^ (String.concat ";\n" 
	    (List.map Pp.pp_unit_clause new_clauses)))); 
        debug (lazy "First superpositions");
        (* We add current to active clauses so that it can be *
         * superposed with itself                             *)
      let alist, atable = 
        current :: alist, IDX.index_unit_clause atable current
      in
        debug (lazy "Indexed");
      let fresh_current, maxvar = Utils.fresh_unit_clause maxvar current in
        (* We need to put fresh_current into the bag so that all *
         * variables clauses refer to are known.                 *)
      let bag, fresh_current = Terms.add_to_bag fresh_current bag in
        (* We superpose current with active clauses *)
      let bag, maxvar, additional_new_clauses =
        superposition_with_table bag maxvar fresh_current atable 
      in
        debug (lazy "Another superposition");
      let new_clauses = new_clauses @ additional_new_clauses in
        (* debug (lazy (Printf.sprintf "Demodulating %d clauses"
                 (List.length new_clauses))); *)
      let bag, new_clauses = 
        HExtlib.filter_map_monad (simplify atable maxvar) bag new_clauses
      in
        debug (lazy "Demodulated new clauses");
      bag, maxvar, (alist, atable), new_clauses
    ;;

    let prof_ir = HExtlib.profile ~enable "infer_right";;
    let infer_right bag maxvar current t = 
      prof_ir.HExtlib.profile (infer_right bag maxvar current) t
    ;;

    let infer_left bag maxvar goal (_alist, atable) =
        (* We superpose the goal with active clauses *)
     if (match goal with (_,_,[],_) -> true | _ -> false) then bag, maxvar, []
     else
      let bag, maxvar, new_goals =        
        superposition_with_table bag maxvar goal atable 
      in
        debug(lazy  "Superposed goal with active clauses");
        (* We simplify the new goals with active clauses *)
      let bag, new_goals = 
        List.fold_left
         (fun (bag, acc) g -> 
            match simplify_goal ~no_demod:false maxvar atable bag [] g with
              | None -> assert false
              | Some (bag,g) -> bag,g::acc)
         (bag, []) new_goals
      in
        debug (lazy "Simplified new goals with active clauses");
      bag, maxvar, List.rev new_goals
    ;;

    let prof_il = HExtlib.profile ~enable "infer_left";;
    let infer_left bag maxvar goal t = 
      prof_il.HExtlib.profile (infer_left bag maxvar goal) t
    ;;

  end
