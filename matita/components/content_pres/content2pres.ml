(* Copyright (C) 2003-2005, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://cs.unibo.it/helm/.
 *)

(***************************************************************************)
(*                                                                         *)
(*                            PROJECT HELM                                 *)
(*                                                                         *)
(*                Andrea Asperti <asperti@cs.unibo.it>                     *)
(*                              17/06/2003                                 *)
(*                                                                         *)
(***************************************************************************)

(* $Id: content2pres.ml 11792 2012-01-12 12:03:29Z ricciott $ *)

module P = Mpresentation
module B = Box
module Con = Content

let p_mtr a b = Mpresentation.Mtr(a,b)
let p_mtd a b = Mpresentation.Mtd(a,b)
let p_mtable a b = Mpresentation.Mtable(a,b)
let p_mtext a b = Mpresentation.Mtext(a,b)
let p_mi a b = Mpresentation.Mi(a,b)
let p_mo a b = Mpresentation.Mo(a,b)
let p_mrow a b = Mpresentation.Mrow(a,b)
let p_mphantom a b = Mpresentation.Mphantom(a,b)
let b_ink a = Box.Ink a

let rec split n l =
  if n = 0 then [],l
  else let l1,l2 = 
    split (n-1) (List.tl l) in
    (List.hd l)::l1,l2
  
let get_xref = function
  | `Declaration d  
  | `Hypothesis d -> d.Con.dec_id
  | `Proof p -> p.Con.proof_id
  | `Definition d -> d.Con.def_id
  | `Joint jo -> jo.Con.joint_id

let hv_attrs =
  RenderingAttrs.spacing_attributes `BoxML
  @ RenderingAttrs.indent_attributes `BoxML

let make_row items concl =
  B.b_hv hv_attrs (items @ [ concl ])
(*   match concl with 
      B.V _ -> |+ big! +|
        B.b_v attrs [B.b_h [] items; B.b_indent concl]
    | _ ->  |+ small +|
        B.b_h attrs (items@[B.b_space; concl]) *)

let make_concl ?(attrs=[]) verb concl =
  B.b_hv (hv_attrs @ attrs) [ B.b_kw verb; concl ]
(*   match concl with 
      B.V _ -> |+ big! +|
        B.b_v attrs [ B.b_kw verb; B.b_indent concl]
    | _ ->  |+ small +|
        B.b_h attrs [ B.b_kw verb; B.b_space; concl ] *)

let make_args_for_apply term2pres args =
 let make_arg_for_apply is_first arg row = 
  let res =
   match arg with 
      Con.Aux n -> assert false
    | Con.Premise prem -> 
        let name = 
          (match prem.Con.premise_binder with
             None -> "previous"
           | Some s -> s) in
        (B.b_object (P.Mi ([], name)))::row
    | Con.Lemma lemma -> 
        let lemma_attrs = [
          Some "helm", "xref", lemma.Con.lemma_id;
          Some "xlink", "href", lemma.Con.lemma_uri ]
        in
        (B.b_object (P.Mi(lemma_attrs,lemma.Con.lemma_name)))::row 
    | Con.Term (b,t) -> 
        if is_first || (not b) then
          (term2pres t)::row
        else (B.b_object (P.Mi([],"?")))::row
    | Con.ArgProof _ 
    | Con.ArgMethod _ -> 
	(B.b_object (P.Mi([],"?")))::row
  in
   if is_first then res else B.skip::res
 in
  match args with 
    hd::tl -> 
      make_arg_for_apply true hd 
        (List.fold_right (make_arg_for_apply false) tl [])
  | _ -> assert false

let get_name ?(default="_") = function
  | Some s -> s
  | None -> default

let add_xref id = function
  | B.Text (attrs, t) -> B.Text (((Some "helm", "xref", id) :: attrs), t)
  | _ -> assert false (* TODO, add_xref is meaningful for all boxes *)

let rec justification ~for_rewriting_step ~ignore_atoms term2pres p = 
  if p.Con.proof_conclude.Con.conclude_method = "Exact" &&
     ignore_atoms
  then
   [], None
  else if
   (p.Con.proof_conclude.Con.conclude_method = "Exact" && not ignore_atoms) ||
   (p.Con.proof_context = [] &&
    p.Con.proof_apply_context = [] &&
    p.Con.proof_conclude.Con.conclude_method = "Apply")
  then
    let pres_args = 
      make_args_for_apply term2pres p.Con.proof_conclude.Con.conclude_args
    in
     [B.H([],
     (*(if for_rewriting_step then (B.b_kw "exact") else (B.b_kw "by"))::*)
       (B.b_kw "by")::
       B.b_space::
       B.Text([],"(")::pres_args@[B.Text([],")")])], None 
  else
   [B.H([],
    if for_rewriting_step then
     [B.b_kw "proof"]
    else
     [B.b_kw "by"; B.b_space; B.b_kw "proof"]
    )],
    Some (B.b_toggle [B.b_kw "proof";B.indent (proof2pres true term2pres p)])
     
and proof2pres0 term2pres ?skip_initial_lambdas_internal is_top_down p in_bu_conversion =
    let indent = 
      let is_decl e = 
        (match e with 
           `Declaration _
         | `Hypothesis _ -> true
         | _ -> false) in
      ((List.filter is_decl p.Con.proof_context) != []) in 
    let omit_conclusion = (not indent) && (p.Con.proof_context != []) in
    let concl = 
      (match p.Con.proof_conclude.Con.conclude_conclusion with
         None -> None
       | Some t -> Some (term2pres t)) in
    let body =
        let presconclude = 
          conclude2pres term2pres
          ?skip_initial_lambdas_internal:
            (match skip_initial_lambdas_internal with
                Some (`Later s) -> Some (`Now s)
              | _ -> None)
          is_top_down p.Con.proof_name p.Con.proof_conclude indent
          omit_conclusion in_bu_conversion in
        let presacontext = 
          acontext2pres term2pres
           (if p.Con.proof_conclude.Con.conclude_method = "BU_Conversion" then
             is_top_down
            else
             false)
           p.Con.proof_apply_context
           presconclude indent
           (p.Con.proof_conclude.Con.conclude_method = "BU_Conversion")
        in
        context2pres term2pres
         (match skip_initial_lambdas_internal with
             Some (`Now n) -> snd (HExtlib.split_nth n p.Con.proof_context)
           | _ -> p.Con.proof_context)
          ~continuation:presacontext
    in
(*
let body = B.V([],[B.b_kw ("(*<<" ^ p.Con.proof_conclude.Con.conclude_method ^ (if is_top_down then "(TD)" else "(NTD)") ^ "*)"); body; B.b_kw "(*>>*)"]) in
*)
    match p.Con.proof_name with
      None -> body
    | Some name ->
        let action = 
         match concl with
            None -> body
          | Some ac ->
             let concl =
               make_concl ~attrs:[ Some "helm", "xref", p.Con.proof_id ]
                 "proof of" ac in
             B.b_toggle [ B.H ([], [concl; B.skip ; B.Text([],"(");
                      B.Object ([], P.Mi ([],name));
                      B.Text([],")") ]) ; body ]
        in
         B.indent action

and context2pres term2pres c ~continuation =
    (* we generate a subtable for each context element, for selection
       purposes 
       The table generated by the head-element does not have an xref;
       the whole context-proof is already selectable *)
    match c with
      [] -> continuation
    | hd::tl -> 
        let continuation' =
          List.fold_right
            (fun ce continuation ->
              let xref = get_xref ce in
              B.V([Some "helm", "xref", xref ],
                [B.H([Some "helm", "xref", "ce_"^xref],
                     [ce2pres_in_proof_context_element term2pres ce]);
                 continuation])) tl continuation in
         let hd_xref= get_xref hd in
         B.V([],
             [B.H([Some "helm", "xref", "ce_"^hd_xref],
               [ce2pres_in_proof_context_element term2pres hd]);
             continuation'])
        
and ce2pres_in_joint_context_element term2pres = function
    | `Inductive _ -> assert false (* TODO *)
    | (`Declaration _)
    | (`Hypothesis _)
    | (`Proof _)
    | (`Definition _) as x  -> ce2pres term2pres x
  
and ce2pres_in_proof_context_element term2pres = function 
    | `Joint ho -> 
      B.H ([],(List.map (ce2pres_in_joint_context_element term2pres) ho.Content.joint_defs))
    | (`Declaration _)
    | (`Hypothesis _)
    | (`Proof _)
    | (`Definition _) as x  -> ce2pres term2pres x 
  
and ce2pres term2pres =
    function 
        `Declaration d -> 
         let ty = term2pres d.Con.dec_type in
         B.H ([],
           [(B.b_kw "assume");
            B.b_space;
            B.Object ([], P.Mi([],get_name d.Con.dec_name));
            B.Text([],":");
            ty;
            B.Text([],".")])
      | `Hypothesis h ->
          let ty = term2pres h.Con.dec_type in
          B.H ([],
            [(B.b_kw "suppose");
             B.b_space;
             ty;
             B.b_space;
             B.Text([],"(");
             B.Object ([], P.Mi ([],get_name h.Con.dec_name));
             B.Text([],")");
             B.Text([],".")])
      | `Proof p -> 
           proof2pres0 term2pres false p false
      | `Definition d -> 
          let term = term2pres d.Con.def_term in
          B.H ([],
            [ B.b_kw "let"; B.b_space;
              B.Object ([], P.Mi([],get_name d.Con.def_name));
              B.Text([],Utf8Macro.unicode_of_tex "\\def");
              term])

and acontext2pres term2pres is_top_down ac continuation indent in_bu_conversion =
   let rec aux =
    function
       [] -> continuation
     | p::tl ->
        let continuation = aux tl in
        (* Applicative context get flattened and the "body" of a BU_Conversion
           is put in the applicative context. Thus two different situations
           are possible:
            {method = "BU_Conversion"; applicative_context=[p1; ...; pn]}
            {method = xxx; applicative_context =
              [ p1; ...; pn; {method="BU_Conversion"} ; p_{n+1}; ... ; pm ]}
           In both situations only pn must be processed in in_bu_conversion
           mode
        *)
        let in_bu_conversion =
         match tl with
            [] -> in_bu_conversion
          | p::_ -> p.Con.proof_conclude.Con.conclude_method = "BU_Conversion"
        in
        let hd = proof2pres0 term2pres is_top_down p in_bu_conversion in
        let hd = if indent then B.indent hd else hd in
         B.V([Some "helm","xref",p.Con.proof_id],
          [B.H([Some "helm","xref","ace_"^p.Con.proof_id],[hd]);
           continuation])
   in aux ac

and conclude2pres term2pres ?skip_initial_lambdas_internal is_top_down name conclude indent omit_conclusion in_bu_conversion =
    let tconclude_body = 
      match conclude.Con.conclude_conclusion with
        Some t (*when not omit_conclusion or
         (* CSC: I ignore the omit_conclusion flag in this case.   *)
         (* CSC: Is this the correct behaviour? In the stylesheets *)
         (* CSC: we simply generated nothing (i.e. the output type *)
         (* CSC: of the function should become an option.          *)
         conclude.Con.conclude_method = "BU_Conversion" *) ->
          let concl = term2pres t in 
          if conclude.Con.conclude_method = "BU_Conversion" then
            B.b_hv []
             (make_concl "that is equivalent to" concl ::
                     if is_top_down then [B.b_space ; B.b_kw "done";
                     B.Text([],".")] else [B.Text([],".")])
          else if conclude.Con.conclude_method = "FalseInd" then
           (* false ind is in charge to add the conclusion *)
           falseind term2pres conclude
          else  
            let prequel =
              if
               (not is_top_down) &&
                conclude.Con.conclude_method = "Intros+LetTac"
              then
                let name = get_name name in
                 [B.V ([],
                 [ B.H([],
                    let expected = 
                      (match conclude.Con.conclude_conclusion with 
                         None -> B.Text([],"NO EXPECTED!!!")
                       | Some c -> term2pres c)
                    in
                     [make_concl "we need to prove" expected;
                      B.skip;
                      B.Text([],"(");
                      B.Object ([], P.Mi ([],name));
                      B.Text([],")");
                      B.Text ([],".")
                     ])])]
              else
               [] in
            let conclude_body = 
              conclude_aux term2pres ?skip_initial_lambdas_internal is_top_down conclude in
            let ann_concl = 
              if  conclude.Con.conclude_method = "Intros+LetTac"
               || conclude.Con.conclude_method = "ByInduction"
               || conclude.Con.conclude_method = "TD_Conversion"
               || conclude.Con.conclude_method = "Eq_chain"
              then
               B.Text([],"")
              else if omit_conclusion then 
                B.H([], [B.b_kw "done" ; B.Text([],".") ])
              else
                B.b_hv []
                 ((if not is_top_down || in_bu_conversion then
                    (make_concl "we proved" concl) ::
                      if not is_top_down then
                       let name = get_name ~default:"previous" name in
                        [B.b_space; B.Text([],"(" ^ name ^ ")")]
                      else []
                   else [B.b_kw "done"]
                  ) @ if not in_bu_conversion then [B.Text([],".")] else [])
            in
             B.V ([], prequel @ [conclude_body; ann_concl])
      | _ -> conclude_aux term2pres ?skip_initial_lambdas_internal is_top_down conclude
    in
     if indent then 
       B.indent (B.H ([Some "helm", "xref", conclude.Con.conclude_id],
                     [tconclude_body]))
     else 
       B.H ([Some "helm", "xref", conclude.Con.conclude_id],[tconclude_body])

and conclude_aux term2pres ?skip_initial_lambdas_internal is_top_down conclude =
    if conclude.Con.conclude_method = "TD_Conversion" then
      let expected = 
        (match conclude.Con.conclude_conclusion with 
           None -> B.Text([],"NO EXPECTED!!!")
         | Some c -> term2pres c) in
      let subproof = 
        (match conclude.Con.conclude_args with
          [Con.ArgProof p] -> p
         | _ -> assert false) in
      let synth = 
        (match subproof.Con.proof_conclude.Con.conclude_conclusion with
           None -> B.Text([],"NO SYNTH!!!")
         | Some c -> (term2pres c)) in
      B.V 
        ([],
        [make_concl "we need to  prove" expected;
         B.H ([],[make_concl "or equivalently" synth; B.Text([],".")]);
         proof2pres0 term2pres true subproof false])
    else if conclude.Con.conclude_method = "BU_Conversion" then
      assert false
    else if conclude.Con.conclude_method = "Exact" then
      let arg = 
        (match conclude.Con.conclude_args with 
           [Con.Term (b,t)] -> assert (not b);term2pres t
         | [Con.Premise p] -> 
             (match p.Con.premise_binder with
             | None -> assert false; (* unnamed hypothesis ??? *)
             | Some s -> B.Text([],s))
         | err -> assert false) in
      (match conclude.Con.conclude_conclusion with 
         None ->
          B.b_h [] [B.b_kw "by"; B.b_space; arg]
       | Some c -> 
          B.b_h [] [B.b_kw "by"; B.b_space; arg]
       )
    else if conclude.Con.conclude_method = "Intros+LetTac" then
      (match conclude.Con.conclude_args with
         [Con.ArgProof p] ->
           (match conclude.Con.conclude_args with
              [Con.ArgProof p] -> 
                proof2pres0 term2pres ?skip_initial_lambdas_internal true p false
            | _ -> assert false)
       | _ -> assert false)
(* OLD CODE 
      let conclusion = 
      (match conclude.Con.conclude_conclusion with 
         None -> B.Text([],"NO Conclusion!!!")
       | Some c -> term2pres c) in
      (match conclude.Con.conclude_args with
         [Con.ArgProof p] -> 
           B.V 
            ([None,"align","baseline 1"; None,"equalrows","false";
              None,"columnalign","left"],
              [B.H([],[B.Object([],proof2pres p term2pres false)]);
               B.H([],[B.Object([],
                (make_concl "we proved 1" conclusion))])]);
       | _ -> assert false)
*)
    else if (conclude.Con.conclude_method = "Case") then
      case term2pres conclude
    else if (conclude.Con.conclude_method = "ByInduction") then
      byinduction term2pres conclude
    else if (conclude.Con.conclude_method = "Exists") then
      exists term2pres conclude
    else if (conclude.Con.conclude_method = "AndInd") then
      andind term2pres conclude
    else if (conclude.Con.conclude_method = "FalseInd") then
      falseind term2pres conclude
    else if conclude.Con.conclude_method = "RewriteLR"
         || conclude.Con.conclude_method = "RewriteRL" then
      let justif1,justif2 = 
        (match (List.nth conclude.Con.conclude_args 6) with
           Con.ArgProof p ->
            justification ~for_rewriting_step:true ~ignore_atoms:true
             term2pres p
         | _ -> assert false) in
      let justif =
       match justif2 with
          None -> justif1
        | Some j -> [j]
      in
      let index_term1, index_term2 =
       if conclude.Con.conclude_method = "RewriteLR" then 2,5 else 5,2
      in
      let term1 = 
        (match List.nth conclude.Con.conclude_args index_term1 with
           Con.Term (_,t) -> term2pres t
         | _ -> assert false) in 
      let term2 = 
        (match List.nth conclude.Con.conclude_args index_term2 with
           Con.Term (_,t) -> term2pres t
         | _ -> assert false) in
      let justif =
       match justif with
          [] -> []
        | _ ->
         justif @
          [B.V([],
            [B.b_kw "we proved (" ;
             term1 ;
             B.b_kw "=" ;
             term2; B.b_kw ") (equality)."])]
      in
(*
      B.V ([], 
         B.H ([],[
          (B.b_kw "rewrite");
          B.b_space; term1;
          B.b_space; (B.b_kw "with");
          B.b_space; term2;
          B.b_space; justif1])::
	    match justif2 with None -> [] | Some j -> [B.indent j])
*)
      B.V([], justif @ [B.b_kw "by _"])
    else if conclude.Con.conclude_method = "Eq_chain" then
      let justification p =
       let j1,j2 =
        justification ~for_rewriting_step:true ~ignore_atoms:false term2pres p
       in
        j1, match j2 with Some j -> [j] | None -> []
      in
      let rec aux args =
	match args with
	  | [] -> []
	  | (Con.ArgProof p)::(Con.Term (_,t))::tl -> 
              let justif1,justif2 = justification p in
	       B.HOV(RenderingAttrs.indent_attributes `BoxML,([B.b_kw
               "=";B.b_space;term2pres t;B.b_space]@justif1@
               (if tl <> [] then [B.Text ([],".")] else [B.b_space; B.b_kw "done" ; B.Text([],".")])@
               justif2))::(aux tl)
	  | _ -> assert false 
      in
      let hd = 
	match List.hd conclude.Con.conclude_args with
	  | Con.Term (_,t) -> t 
	  | _ -> assert false 
      in
       if is_top_down then
        B.HOV([],
         [B.b_kw "conclude";B.b_space;term2pres hd;
	  B.V ([],aux (List.tl conclude.Con.conclude_args))])
       else
        B.HOV([],
         [B.b_kw "obtain";B.b_space;B.b_kw "FIXMEXX"; B.b_space;term2pres hd;
	  B.V ([],aux (List.tl conclude.Con.conclude_args))])
    else if conclude.Con.conclude_method = "Apply" then
      let pres_args = 
        make_args_for_apply term2pres conclude.Con.conclude_args in
      B.H([],
        (B.b_kw "by")::
        B.b_space::
        B.Text([],"(")::pres_args@[B.Text([],")")])
    else 
      B.V ([], [
        B.b_kw ("Apply method" ^ conclude.Con.conclude_method ^ " to");
        (B.indent (B.V ([], args2pres term2pres conclude.Con.conclude_args)))])

and args2pres term2pres l = List.map (arg2pres term2pres) l

and arg2pres term2pres =
    function
        Con.Aux n -> B.b_kw ("aux " ^ n)
      | Con.Premise prem -> B.b_kw "premise"
      | Con.Lemma lemma -> B.b_kw "lemma"
      | Con.Term (_,t) -> term2pres t
      | Con.ArgProof p -> proof2pres0 term2pres true p false
      | Con.ArgMethod s -> B.b_kw "method"
 
and case term2pres conclude =
     let proof_conclusion = 
       (match conclude.Con.conclude_conclusion with
          None -> B.b_kw "No conclusion???"
        | Some t -> term2pres t) in
     let arg,args_for_cases = 
       (match conclude.Con.conclude_args with
           Con.Aux(_)::Con.Aux(_)::Con.Term(_)::arg::tl ->
             arg,tl
         | _ -> assert false) in
     let case_on =
       let case_arg = 
         (match arg with
            Con.Aux n -> B.b_kw "an aux???"
           | Con.Premise prem ->
              (match prem.Con.premise_binder with
                 None -> B.b_kw "previous"
               | Some n -> B.Object ([], P.Mi([],n)))
           | Con.Lemma lemma -> B.Object ([], P.Mi([],lemma.Con.lemma_name))
           | Con.Term (_,t) -> 
               term2pres t
           | Con.ArgProof p -> B.b_kw "a proof???"
           | Con.ArgMethod s -> B.b_kw "a method???")
      in
        (make_concl "we proceed by cases on" case_arg) in
     let to_prove =
        (make_concl "to prove" proof_conclusion) in
     B.V ([], case_on::to_prove::(make_cases term2pres args_for_cases))

and byinduction term2pres conclude =
     let proof_conclusion = 
       (match conclude.Con.conclude_conclusion with
          None -> B.b_kw "No conclusion???"
        | Some t -> term2pres t) in
     let inductive_arg,args_for_cases = 
       (match conclude.Con.conclude_args with
           Con.Aux(n)::_::tl ->
             let l1,l2 = split (int_of_string n) tl in
             let last_pos = (List.length l2)-1 in
             List.nth l2 last_pos,l1
         | _ -> assert false) in
     let induction_on =
       let arg = 
         (match inductive_arg with
            Con.Aux n -> B.b_kw "an aux???"
           | Con.Premise prem ->
              (match prem.Con.premise_binder with
                 None -> B.b_kw "previous"
               | Some n -> B.Object ([], P.Mi([],n)))
           | Con.Lemma lemma -> B.Object ([], P.Mi([],lemma.Con.lemma_name))
           | Con.Term (_,t) -> 
               term2pres t
           | Con.ArgProof p -> B.b_kw "a proof???"
           | Con.ArgMethod s -> B.b_kw "a method???") in
        (make_concl "we proceed by induction on" arg) in
     let to_prove =
      B.H ([], [make_concl "to prove" proof_conclusion ; B.Text([],".")]) in
     B.V ([], induction_on::to_prove::(make_cases term2pres args_for_cases))

and make_cases term2pres l = List.map (make_case term2pres) l

and make_case term2pres =
      function 
        Con.ArgProof p ->
          let name =
            (match p.Con.proof_name with
               None -> B.b_kw "no name for case!!"
             | Some n -> B.Object ([], P.Mi([],n))) in
          let indhyps,args =
             List.partition 
               (function
                   `Hypothesis h -> h.Con.dec_inductive
                 | _ -> false) p.Con.proof_context in
          let pattern_aux =
             List.fold_right
               (fun e p -> 
                  let dec  = 
                    (match e with 
                       `Declaration h 
                     | `Hypothesis h -> 
                         let name = get_name h.Con.dec_name in
                         [B.b_space;
                          B.Text([],"(");
                          B.Object ([], P.Mi ([],name));
                          B.Text([],":");
                          (term2pres h.Con.dec_type);
                          B.Text([],")")]
                     | _ -> assert false (*[B.Text ([],"???")]*)) in
                  dec@p) args [] in
          let pattern = 
            B.H ([],
               (B.b_kw "case"::B.b_space::name::pattern_aux)@
                [B.b_space;
                 B.Text([], ".")]) in
          let subconcl = 
            (match p.Con.proof_conclude.Con.conclude_conclusion with
               None -> B.b_kw "No conclusion!!!"
             | Some t -> term2pres t) in
          let asubconcl = B.indent (make_concl "the thesis becomes" subconcl) in
          let induction_hypothesis = 
            (match indhyps with
              [] -> []
            | _ -> 
               let text = B.indent (B.b_kw "by induction hypothesis we know") in
               let make_hyp =
                 function 
                   `Hypothesis h ->
                     let name = 
                       (match h.Con.dec_name with
                          None -> "useless"
                        | Some s -> s) in
                     B.indent (B.H ([],
                       [term2pres h.Con.dec_type;
                        B.b_space;
                        B.Text([],"(");
                        B.Object ([], P.Mi ([],name));
                        B.Text([],")");
                        B.Text([],".")]))
                   | _ -> assert false in
               let hyps = List.map make_hyp indhyps in
               text::hyps) in          
          let body =
           conclude2pres term2pres true p.Con.proof_name p.Con.proof_conclude true true false in
          let presacontext = 
           let acontext_id =
            match p.Con.proof_apply_context with
               [] -> p.Con.proof_conclude.Con.conclude_id
             | {Con.proof_id = id}::_ -> id
           in
            B.Action([None,"type","toggle"],
              [ B.indent (add_xref acontext_id (B.b_kw "Proof"));
                acontext2pres term2pres
                 (p.Con.proof_conclude.Con.conclude_method = "BU_Conversion")
                 p.Con.proof_apply_context body true
                 (p.Con.proof_conclude.Con.conclude_method = "BU_Conversion")
              ]) in
          B.V ([], pattern::induction_hypothesis@[B.H ([],[asubconcl;B.Text([],".")]);presacontext])
       | _ -> assert false 

and falseind term2pres conclude =
       let proof_conclusion = 
         (match conclude.Con.conclude_conclusion with
            None -> B.b_kw "No conclusion???"
          | Some t -> term2pres t) in
       let case_arg = 
         (match conclude.Con.conclude_args with
             [Con.Aux(n);_;case_arg] -> case_arg
           | _ -> assert false;
             (* 
             List.map (ContentPp.parg 0) conclude.Con.conclude_args;
             assert false *)) in
       let arg = 
         (match case_arg with
             Con.Aux n -> assert false
           | Con.Premise prem ->
              (match prem.Con.premise_binder with
                 None -> [B.b_kw "Contradiction, hence"]
               | Some n -> 
                   [ B.Object ([],P.Mi([],n)); B.skip;
                     B.b_kw "is contradictory, hence"])
           | Con.Lemma lemma -> 
               [ B.Object ([], P.Mi([],lemma.Con.lemma_name)); B.skip;
                 B.b_kw "is contradictory, hence" ]
           | _ -> assert false) in
       make_row arg proof_conclusion

and andind term2pres conclude =
       let proof,case_arg = 
         (match conclude.Con.conclude_args with
             [Con.Aux(n);_;Con.ArgProof proof;case_arg] -> proof,case_arg
           | _ -> assert false;
             (* 
             List.map (ContentPp.parg 0) conclude.Con.conclude_args;
             assert false *)) in
       let arg = 
         (match case_arg with
             Con.Aux n -> assert false
           | Con.Premise prem ->
              (match prem.Con.premise_binder with
                 None -> []
               | Some n -> [(B.b_kw "by"); B.b_space; B.Object([], P.Mi([],n))])
           | Con.Lemma lemma -> 
               [(B.b_kw "by");B.skip;
                B.Object([], P.Mi([],lemma.Con.lemma_name))]
           | _ -> assert false) in
       match proof.Con.proof_context with
         `Hypothesis hyp1::`Hypothesis hyp2::tl ->
            let preshyp1 = 
              B.H ([],
               [B.Text([],"(");
                B.Object ([], P.Mi([],get_name hyp1.Con.dec_name));
                B.Text([],")");
                B.skip;
                term2pres hyp1.Con.dec_type]) in
            let preshyp2 = 
              B.H ([],
               [B.Text([],"(");
                B.Object ([], P.Mi([],get_name hyp2.Con.dec_name));
                B.Text([],")");
                B.skip;
                term2pres hyp2.Con.dec_type]) in
            let body =
             conclude2pres term2pres false proof.Con.proof_name proof.Con.proof_conclude
              false true false in
            let presacontext = 
              acontext2pres term2pres false proof.Con.proof_apply_context body false false
            in
            B.V 
              ([],
               [B.H ([],arg@[B.skip; B.b_kw "we have"]);
                preshyp1;
                B.b_kw "and";
                preshyp2;
                presacontext]);
         | _ -> assert false

and exists term2pres conclude =
       let proof = 
         (match conclude.Con.conclude_args with
             [Con.Aux(n);_;Con.ArgProof proof;_] -> proof
           | _ -> assert false;
             (* 
             List.map (ContentPp.parg 0) conclude.Con.conclude_args;
             assert false *)) in
       match proof.Con.proof_context with
           `Declaration decl::`Hypothesis hyp::tl
         | `Hypothesis decl::`Hypothesis hyp::tl ->
           let presdecl = 
             B.H ([],
               [(B.b_kw "let");
                B.skip;
                B.Object ([], P.Mi([],get_name decl.Con.dec_name));
                B.Text([],":"); term2pres decl.Con.dec_type]) in
           let suchthat =
             B.H ([],
               [(B.b_kw "such that");
                B.skip;
                B.Text([],"(");
                B.Object ([], P.Mi([],get_name hyp.Con.dec_name));
                B.Text([],")");
                B.skip;
                term2pres hyp.Con.dec_type]) in
            let body =
             conclude2pres term2pres false proof.Con.proof_name proof.Con.proof_conclude
              false true false in
            let presacontext = 
              acontext2pres term2pres false proof.Con.proof_apply_context body false false
            in
            B.V 
              ([],
               [presdecl;
                suchthat;
                presacontext]);
         | _ -> assert false

and proof2pres ?skip_initial_lambdas is_top_down term2pres p =
  proof2pres0 term2pres
   ?skip_initial_lambdas_internal:
     (match skip_initial_lambdas with
         None -> Some (`Later 0) (* we already printed theorem: *)
       | Some n -> Some (`Later n))
   is_top_down p false

exception ToDo

let counter = ref 0

let conjecture2pres term2pres (id, n, context, ty) =
 B.b_indent
  (B.b_hv [Some "helm", "xref", id]
     ((B.b_toggle [
        B.b_h [] [B.b_text [] "{...}"; B.b_space];
        B.b_hv [] (HExtlib.list_concat ~sep:[B.b_text [] ";"; B.b_space] 
         (List.map (fun x -> [x])
         (List.map
          (function
             | None ->
		 B.b_h []
                   [ B.b_object (p_mi [] "_") ;
                     B.b_object (p_mo [] ":?") ;
                     B.b_object (p_mi [] "_")]
             | Some (`Declaration d)
             | Some (`Hypothesis d) ->
		 let { Content.dec_name =
		     dec_name ; Content.dec_type = ty } = d
		 in
		   B.b_h []
                     [ B.b_object
			 (p_mi []
			    (match dec_name with
				 None -> "_"
			       | Some n -> n));
                       B.b_text [] ":"; B.b_space; 
                       term2pres ty ]
             | Some (`Definition d) ->
                 let
                     { Content.def_name = def_name ;
                       Content.def_term = bo } = d
                 in
                   B.b_h []
                     [ B.b_object (p_mi []
				     (match def_name with
					  None -> "_"
					| Some n -> n)) ;
                       B.b_text [] (Utf8Macro.unicode_of_tex "\\Assign");
                       B.b_space;
                       term2pres bo]
             | Some (`Proof p) ->
                 let proof_name = p.Content.proof_name in
                   B.b_h []
                     [ B.b_object (p_mi []
				     (match proof_name with
					  None -> "_"
					| Some n -> n)) ;
                       B.b_text [] (Utf8Macro.unicode_of_tex "\\Assign");
                       B.b_space;
                       proof2pres true term2pres p])
          (List.rev context)))) ] ::
         [ B.b_h []
           [ B.b_space; 
             B.b_text [] (Utf8Macro.unicode_of_tex "\\vdash");
             B.b_space;
             B.b_object (p_mi [] (string_of_int n)) ;
             B.b_text [] ":" ;
             B.b_space;
             term2pres ty ]])))

let metasenv2pres term2pres = function
  | None -> []
  | Some metasenv' ->
      (* Conjectures are in their own table to make *)
      (* diffing the DOM trees easier.              *)
      [B.b_v []
        ((B.b_kw ("Conjectures:" ^
            (let _ = incr counter; in (string_of_int !counter)))) ::
         (List.map (conjecture2pres term2pres) metasenv'))]

let inductive2pres term2pres ind =
  let constructor2pres decl =
    B.b_h [] [
      B.b_text [] ("| " ^ get_name decl.Content.dec_name ^ ":");
      B.b_space;
      term2pres decl.Content.dec_type
    ]
  in
  B.b_v []
    (B.b_h [] [
      B.b_kw (ind.Content.inductive_name ^ " of arity");
      B.smallskip;
      term2pres ind.Content.inductive_type ]
    :: List.map constructor2pres ind.Content.inductive_constructors)

let definition2pres ?recno term2pres d =
  let name = match d.Content.def_name with Some x -> x|_->assert false in
  let rno = match recno with None -> -1 (* cofix *) | Some x -> x in
  let ty = d.Content.def_type in
  let module P = NotationPt in
  let rec split_pi i t =
    (* dummy case for corecursive defs *)
    if i = ~-1 then [], P.UserInput, t
    else if i <= 1 then 
      match t with 
      | P.Binder ((`Pi|`Forall),(var,_ as v),t) 
      | P.AttributedTerm (_,P.Binder ((`Pi|`Forall),(var,_ as v),t)) -> 
            [v], var, t 
      | _ -> assert false
    else
      match t with
      | P.Binder ((`Pi|`Forall), var ,ty) 
      | P.AttributedTerm (_, P.Binder ((`Pi|`Forall), var ,ty)) ->
           let l, r, t = split_pi (i-1) ty in
           var :: l, r, t
      | _ -> assert false
  in 
  let params, rec_param, ty = split_pi rno ty in
  let body = d.Content.def_term in
  let params = 
    List.map 
      (function 
      | (name,Some ty) -> 
          B.b_h [] [B.b_text [] "("; term2pres name; B.b_text [] " : ";
                    B.b_space; term2pres ty; B.b_text [] ")"; B.b_space]
      | (name,None) -> B.b_h [] [term2pres name;B.b_space]) 
      params
  in
  B.b_hv [] 
   [B.b_hov (RenderingAttrs.indent_attributes `BoxML)
    ( [B.b_hov (RenderingAttrs.indent_attributes `BoxML) ([ B.b_space; B.b_text [] name ] @ 
        if params <> [] then
           [B.indent(B.b_hov (RenderingAttrs.indent_attributes `BoxML) (params))]
        else [])] 
      @ [B.b_h [] 
         ((if rno <> -1 then 
           [B.b_kw "on";B.b_space;term2pres rec_param] else [])
         @ [ B.b_space; B.b_text [] ":";]) ]
      @[ B.indent(term2pres ty)]); 
   B.b_text [] ":=";
   B.b_h [] [B.b_space;term2pres body] ]
;;

let njoint_def2pres ?recno term2pres def =
  match def with
  | `Inductive ind -> inductive2pres term2pres ind
  | `Definition def -> definition2pres ?recno term2pres def 
  | _ -> assert false
;;

let njoint_def2pres term2pres joint_kind defs =
  match joint_kind with
  | `Recursive recnos ->
      B.b_hv [] (B.b_kw "nlet rec " ::
        List.flatten
         (HExtlib.list_mapi (fun x i -> 
            if i > 0 then [B.b_kw " and ";x] else [x])
          (List.map2 (fun a b -> njoint_def2pres ~recno:a term2pres b) 
            recnos defs)))
  | `CoRecursive ->
      B.b_hv [] (B.b_kw "nlet corec " ::
        List.flatten
         (HExtlib.list_mapi (fun x i -> 
            if i > 0 then [B.b_kw " and ";x] else [x])
          (List.map (njoint_def2pres term2pres) defs)))
  | `Inductive _ -> 
      B.b_hv [] (B.b_kw "ninductive " ::
        List.flatten
         (HExtlib.list_mapi (fun x i -> 
            if i > 0 then [B.b_kw " and ";x] else [x])
          (List.map (njoint_def2pres term2pres) defs)))
  | `CoInductive _ -> 
      B.b_hv [] (B.b_kw "ncoinductive " ::
        List.flatten
         (HExtlib.list_mapi (fun x i -> 
            if i > 0 then [B.b_kw " and ";x] else [x])
          (List.map (njoint_def2pres term2pres) defs)))
;;

let nobj2pres0
  ?skip_initial_lambdas ?(skip_thm_and_qed=false) term2pres 
  (id,metasenv,obj : NotationPt.term Content.cobj) 
=
  match obj with
  | `Def (Content.Const, thesis, `Proof p) ->
      let name = get_name p.Content.proof_name in
      let proof = proof2pres true ?skip_initial_lambdas term2pres p in
      if skip_thm_and_qed then
        proof
      else
      B.b_v
        [Some "helm","xref","id"]
        ([ B.b_h [] (B.b_kw ("ntheorem " ^ name) :: 
          [B.b_kw ":"]);
           B.H ([],[B.indent (term2pres thesis) ; B.b_kw "." ])] @
         metasenv2pres term2pres metasenv @
         [proof ; B.b_kw "qed."])
  | `Def (_, ty, `Definition body) ->
      let name = get_name body.Content.def_name in
      B.b_v
        [Some "helm","xref","id"]
        ([B.b_h []
           (B.b_kw ("ndefinition " ^ name) :: [B.b_kw ":"]);
          B.indent (term2pres ty)] @
          metasenv2pres term2pres metasenv @
          [B.b_kw ":=";
           B.indent (term2pres body.Content.def_term);
           B.b_kw "."])
  | `Decl (_, `Declaration decl)
  | `Decl (_, `Hypothesis decl) ->
      let name = get_name decl.Content.dec_name in
      B.b_v
        [Some "helm","xref","id"]
        ([B.b_h [] (B.b_kw ("naxiom " ^ name) :: []);
          B.b_kw "Type:";
          B.indent (term2pres decl.Content.dec_type)] @
          metasenv2pres term2pres metasenv)
  | `Joint joint ->
      B.b_v [] 
        [njoint_def2pres term2pres 
          joint.Content.joint_kind joint.Content.joint_defs]
  | _ -> raise ToDo

let nterm2pres status ~ids_to_nrefs =
 let lookup_uri id =
  try
   let nref = Hashtbl.find ids_to_nrefs id in
    Some (NReference.string_of_reference nref)
  with Not_found -> None
 in
  fun ?(prec=90) ast ->
   CicNotationPres.box_of_mpres
    (CicNotationPres.render status ~lookup_uri ~prec
      (TermContentPres.pp_ast status ast))

let nobj2pres status ~ids_to_nrefs =
 nobj2pres0 ?skip_initial_lambdas:None ?skip_thm_and_qed:None
  (nterm2pres status ~ids_to_nrefs)

let nconjlist2pres0 term2pres context = 
 let rec aux accum =
  function 
    [] -> accum 
  | None::tl -> aux accum tl
  | (Some (`Declaration d))::tl ->
      let
        { Con.dec_name = dec_name ;
          Con.dec_id = dec_id ;
          Con.dec_type = ty } = d in
      let r = 
        Box.b_hv [Some "helm", "xref", dec_id] 
          [ Box.b_h []
            [ Box.b_object (p_mi []
               (match dec_name with
                  None -> "_"
               | Some n -> n)) ;
              Box.b_space; Box.b_text [] ":"; ];
	      Box.indent (term2pres ty)] in
      aux (r::accum) tl
  | (Some (`Definition d))::tl ->
      let
        { Con.def_name = def_name ;
          Con.def_id = def_id ;
          Con.def_term = bo } = d in
      let r = 
        Box.b_hov [Some "helm", "xref", def_id]
           [ Box.b_object (p_mi []
             (match def_name with
                None -> "_"
              | Some n -> n)) ; Box.b_space ;
             Box.b_text [] (Utf8Macro.unicode_of_tex "\\def") ;
             Box.indent (term2pres bo)] in
      aux (r::accum) tl
   | _::_ -> assert false
 in
  if context <> [] then [Box.b_v [] (aux [] context)] else []

let sequent2pres0 term2pres (_,_,context,ty) =
 let pres_context = nconjlist2pres0 term2pres context in
 let pres_goal = term2pres ty in 
 (Box.b_h [] [
   Box.b_space; 
   (Box.b_v []
      (Box.b_space ::
       pres_context @ [
       b_ink [None,"width","4cm"; None,"height","2px"]; (* sequent line *)
       Box.b_space; 
       pres_goal]))])

let ncontext2pres status ~ids_to_nrefs ctx =
 let ctx = HExtlib.filter_map (fun x -> x) ctx in
 context2pres (nterm2pres status ~ids_to_nrefs) ~continuation:Box.smallskip
  (ctx:>NotationPt.term Con.in_proof_context_element list)

let nsequent2pres status ~ids_to_nrefs =
 sequent2pres0 (nterm2pres status ~ids_to_nrefs)
