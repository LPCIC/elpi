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

(* $Id: orderings.ml 9869 2009-06-11 22:52:38Z denes $ *)

type eq_sig_type = Eq | EqInd_l | EqInd_r | Refl
              
let eqsig = ref (fun _ -> assert false);;
let set_sig f = eqsig:= f;;
let get_sig = fun x -> !eqsig x;;

let default_sig = function
  | Eq -> 
      let uri = NUri.uri_of_string "cic:/matita/basics/logic/eq.ind" in
      let ref = NReference.reference_of_spec uri (NReference.Ind(true,0,2)) in
        NCic.Const ref
  | EqInd_l -> 
      let uri = NUri.uri_of_string "cic:/matita/basics/logic/rewrite_l.con" in
      let ref = NReference.reference_of_spec uri (NReference.Def(1)) in
        NCic.Const ref
  | EqInd_r -> 
      let uri = NUri.uri_of_string "cic:/matita/basics/logic/rewrite_r.con" in
      let ref = NReference.reference_of_spec uri (NReference.Def(3)) in
        NCic.Const ref
  | Refl ->
      let uri = NUri.uri_of_string "cic:/matita/basics/logic/eq.ind" in
      let ref = NReference.reference_of_spec uri (NReference.Con(0,1,2)) in
        NCic.Const ref

let set_default_sig () =
  (*prerr_endline "setting default sig";*)
  eqsig := default_sig

(* let debug c r = prerr_endline r; c *)
let debug c _ = c;;

  let eqP() = debug (!eqsig Eq) "eq"  ;;
  let eq_ind() = debug (!eqsig EqInd_l) "eq_ind" ;;
  let eq_ind_r() = debug (!eqsig EqInd_r) "eq_ind_r";; 
  let eq_refl() = debug (!eqsig Refl) "refl";;


  let extract status lift vl t =
    let rec pos i = function 
      | [] -> raise Not_found 
      | j :: tl when j <> i -> 1+ pos i tl
      | _ -> 1
    in
    let vl_len = List.length vl in
    let rec extract = function
      | Terms.Leaf x -> NCicSubstitution.lift status (vl_len+lift) x
      | Terms.Var j -> 
           (try NCic.Rel (pos j vl) with Not_found -> NCic.Implicit `Term) 
      | Terms.Node l -> NCic.Appl (List.map extract l)
    in
      extract t
  ;;

   let mk_predicate status hole_type amount ft p1 vl =
    let rec aux t p = 
      match p with
      | [] -> NCic.Rel 1
      | n::tl ->
          match t with
          | Terms.Leaf _ 
          | Terms.Var _ -> 
              let module NCicBlob = NCicBlob.NCicBlob(
                        struct
                          let metasenv = [] let subst = [] let context = []
                        end)
                          in
              let module Pp = Pp.Pp(NCicBlob) in  
               (* prerr_endline ("term: " ^ Pp.pp_foterm ft); 
                  prerr_endline ("path: " ^ String.concat "," 
                 (List.map string_of_int p1));
               prerr_endline ("leading to: " ^ Pp.pp_foterm t); *)
               assert false
          | Terms.Node l -> 
              let l = 
                HExtlib.list_mapi
                  (fun t i -> 
                    if i = n then aux t tl 
                    else extract status amount (0::vl) t)
                  l
              in            
              NCic.Appl l
    in
      NCic.Lambda("x", hole_type, aux ft (List.rev p1))
    ;;

  let dag = 
   let uri = NUri.uri_of_string "cic:/matita/ng/sets/setoids/prop1.con" in
   let ref = NReference.reference_of_spec uri (NReference.Fix(0,2,4)) in
     NCic.Const ref
  ;;

  (*
  let eq_setoid = 
   let uri = NUri.uri_of_string "cic:/matita/ng/sets/setoids/eq.con" in
   let ref = NReference.reference_of_spec uri (NReference.Fix(0,0,2)) in
     NCic.Const ref
  ;;
  *)

  let sym eq = 
   let u= NUri.uri_of_string "cic:/matita/ng/properties/relations/sym.con" in
   let u = NReference.reference_of_spec u (NReference.Fix(0,1,3)) in
     NCic.Appl[NCic.Const u; NCic.Implicit `Type; NCic.Implicit `Term;
     NCic.Implicit `Term; NCic.Implicit `Term; eq]; 
  ;;

  let eq_morphism1 eq = 
   let u= NUri.uri_of_string "cic:/matita/ng/sets/setoids/eq_is_morphism1.con" in
   let u = NReference.reference_of_spec u (NReference.Def 4) in
     NCic.Appl[NCic.Const u; NCic.Implicit `Term; NCic.Implicit `Term;
     NCic.Implicit `Term; NCic.Implicit `Term; eq]; 
  ;;

  let eq_morphism2 eq = 
   let u= NUri.uri_of_string "cic:/matita/ng/sets/setoids/eq_is_morphism2.con" in
   let u = NReference.reference_of_spec u (NReference.Def 4) in
     NCic.Appl[NCic.Const u; NCic.Implicit `Term; NCic.Implicit `Term;
     NCic.Implicit `Term; eq; NCic.Implicit `Term]; 
  ;;

  let trans eq p = 
   let u= NUri.uri_of_string "cic:/matita/ng/properties/relations/trans.con" in
   let u = NReference.reference_of_spec u (NReference.Fix(0,1,3)) in
     NCic.Appl[NCic.Const u; NCic.Implicit `Type; NCic.Implicit `Term;
     NCic.Implicit `Term; NCic.Implicit `Term; NCic.Implicit `Term; eq]
  ;;

  let iff1 eq p = 
   let uri = NUri.uri_of_string "cic:/matita/ng/logic/connectives/if.con" in
   let ref = NReference.reference_of_spec uri (NReference.Fix(0,2,1)) in
     NCic.Appl[NCic.Const ref; NCic.Implicit `Type; NCic.Implicit `Type; 
	       eq; p]; 
  ;;

(*
  let mk_refl = function
      | NCic.Appl [_; _; x; _] -> 
   let uri= NUri.uri_of_string "cic:/matita/ng/properties/relations/refl.con" in
   let ref = NReference.reference_of_spec uri (NReference.Fix(0,1,3)) in
    NCic.Appl[NCic.Const ref; NCic.Implicit `Type; NCic.Implicit `Term;
    NCic.Implicit `Term(*x*)]
      | _ -> assert false
*)   

  let mk_refl = function
    | NCic.Appl [_; ty; l; _]
      -> NCic.Appl [eq_refl();ty;l]
    | _ -> assert false


   let mk_morphism status eq amount ft pl vl =
    let rec aux t p = 
      match p with
      | [] -> eq
      | n::tl ->
          prerr_endline (string_of_int n);
          match t with
          | Terms.Leaf _ 
          | Terms.Var _ -> assert false
          | Terms.Node [] -> assert false
          | Terms.Node [ Terms.Leaf eqt ; _; l; r ]
             when (eqP ()) = eqt ->
               if n=2 then eq_morphism1 (aux l tl)
               else eq_morphism2 (aux r tl)
          | Terms.Node (f::l) ->
             snd (
              List.fold_left
               (fun (i,acc) t ->
                 i+1,
                  let f = extract status amount vl f in
                  if i = n then
                   let imp = NCic.Implicit `Term in
                    NCic.Appl (dag::imp::imp::imp(* f *)::imp::imp::
                               [aux t tl])
                  else
                    NCicUntrusted.mk_appl acc [extract status amount vl t]
               ) (1,extract status amount vl f) l)
    in aux ft (List.rev pl)
    ;;

  let mk_proof status ?(demod=false) (bag : NCic.term Terms.bag) mp subst steps=
    let module NCicBlob = 
       NCicBlob.NCicBlob(
	 struct
	   let metasenv = [] let subst = [] let context = []
	 end)
     in
     let  module Pp = Pp.Pp(NCicBlob) 
     in
    let module Subst = FoSubst in
    let compose subst1 subst2 =
      let s1 = List.map (fun (x,t) -> (x, Subst.apply_subst subst2 t)) subst1 in
      let s2 = List.filter (fun (m,_) -> not (List.mem_assoc m s1)) subst2
      in s1 @ s2
    in
    let position i l = 
      let rec aux = function
       | [] -> assert false
       | (j,_) :: tl when i = j -> 1
       | _ :: tl -> 1 + aux tl
      in
        aux l
    in
    let vars_of i l = fst (List.assoc i l) in
    let ty_of i l = snd (List.assoc i l) in
    let close_with_lambdas vl t = 
      List.fold_left 
       (fun t i -> 
          NCic.Lambda ("x"^string_of_int i, NCic.Implicit `Type, t))
       t vl  
    in
    let close_with_forall vl t = 
      List.fold_left 
       (fun t i -> 
          NCic.Prod ("x"^string_of_int i, NCic.Implicit `Type, t))
       t vl  
    in
    let get_literal id =
      let (_, lit, vl, proof),_,_ = Terms.get_from_bag id bag in
      let lit =match lit with 
          | Terms.Predicate t -> t (* assert false *) 
          | Terms.Equation (l,r,ty,_) -> 
              Terms.Node [ Terms.Leaf eqP(); ty; l; r]
      in
        lit, vl, proof
    in
    let proof_type =
      let lit,_,_ = get_literal mp in
      let lit = Subst.apply_subst subst lit in
        extract status 0 [] lit in
    (* composition of all subst acting on goal *)
    let res_subst = subst
    in
    let rec aux ongoal seen = function
      | [] -> NCic.Rel 1
      | id :: tl ->
          let amount = List.length seen in
          let lit,vl,proof = get_literal id in
          if not ongoal && id = mp then
            let lit = Subst.apply_subst subst lit in 
            let eq_ty = extract status amount [] lit in
            let refl = 
	      if demod then NCic.Implicit `Term 
	      else mk_refl eq_ty in
              (* prerr_endline ("Reached m point, id=" ^ (string_of_int id));
                (NCic.LetIn ("clause_" ^ string_of_int id, eq_ty, refl,
                aux true ((id,([],lit))::seen) (id::tl))) *)
              let res = NCicSubstitution.subst status
                ~avoid_beta_redexes:true ~no_implicit:false refl
                (aux true ((id,([],lit))::seen) (id::tl))
              in res
          else
          match proof with
          | Terms.Exact _ when tl=[] ->
              (* prerr_endline ("Exact (tl=[]) for " ^ (string_of_int id)); *)
              aux ongoal seen tl
          | Terms.Step _ when tl=[] -> assert false
          | Terms.Exact ft ->
	      (*
               prerr_endline ("Exact for " ^ (string_of_int id));
               NCic.LetIn ("clause_" ^ string_of_int id, 
                 close_with_forall vl (extract status amount vl lit),
                 close_with_lambdas vl (extract status amount vl ft),
                 aux ongoal 
                   ((id,(List.map (fun x -> Terms.Var x) vl,lit))::seen) tl)
               *)
               let res = NCicSubstitution.subst status
                 ~avoid_beta_redexes:true ~no_implicit:false
                 (close_with_lambdas vl (extract status amount vl ft))
                 (aux ongoal 
                   ((id,(List.map (fun x -> Terms.Var x) vl,lit))::seen) tl)
               in res 
          | Terms.Step (_, id1, id2, dir, pos, subst) ->
              (* prerr_endline (if ongoal then "on goal" else "not on goal");
                 prerr_endline (Pp.pp_substitution subst); *)
              (* let subst = if ongoal then res_subst else subst in *)
              let id, id1,(lit,vl,proof) =
                if ongoal then
		  let lit,vl,proof = get_literal id1 in
		  id1,id,(Subst.apply_subst res_subst lit,
                          Subst.filter res_subst vl, proof)
                else id,id1,(lit,vl,proof) in
              (* free variables remaining in the goal should not
                 be abstracted: we do not want to prove a generalization *)
              (* prerr_endline ("variables = " ^ String.concat ","
                (List.map string_of_int vl)); *)
              let vl = if ongoal then [] else vl in 
              let proof_of_id id = 
                let vars = List.rev (vars_of id seen) in
                let args = List.map (Subst.apply_subst subst) vars in
                let args = List.map (extract status amount vl) args in
                let rel_for_id = NCic.Rel (List.length vl + position id seen) in
                  if args = [] then rel_for_id                    
                  else NCic.Appl (rel_for_id::args)
              in
              let p_id1 = proof_of_id id1 in
              let p_id2 = proof_of_id id2 in
              let pred, hole_type, l, r = 
                let id1_ty = ty_of id1 seen in
                let id2_ty,l,r = 
                  match ty_of id2 seen with
                  | Terms.Node [ _; t; l; r ] -> 
                      extract status amount vl (Subst.apply_subst subst t),
                      extract status amount vl (Subst.apply_subst subst l),
                      extract status amount vl (Subst.apply_subst subst r)
                  | _ -> assert false
                in
                (* let _ = prerr_endline ("body = " ^(Pp.pp_foterm id1_ty)) 
                   in *)
		mk_predicate status
                  id2_ty amount (Subst.apply_subst subst id1_ty) pos vl,
                id2_ty,
                l,r
              in
              let rewrite_step =
		if (ongoal=true) = (dir=Terms.Left2Right) then
		  NCic.Appl 
                    [eq_ind_r(); hole_type; r; pred; p_id1; l; p_id2]
		else
		  NCic.Appl 
                    [ eq_ind(); hole_type; l; pred; p_id1; r; p_id2]
	      in
              let body = aux ongoal 
                ((id,(List.map (fun x -> Terms.Var x) vl,lit))::seen) tl 
              in 
	      let occ =
               NCicUntrusted.count_occurrences status [] 1 body in
		if occ <= 1 then
                  NCicSubstitution.subst status
                    ~avoid_beta_redexes:true ~no_implicit:false
                    (close_with_lambdas vl rewrite_step) body
                else
                  NCic.LetIn ("clause_" ^ string_of_int id, 
                    close_with_forall vl (extract status amount vl lit),
                           (* NCic.Implicit `Type, *)
                    close_with_lambdas vl rewrite_step, body)
    in 
      aux false [] steps, proof_type
  ;;

