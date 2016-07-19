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

(* $Id: nCic.ml 9058 2008-10-13 17:42:30Z tassi $ *)

let fresh_name =
 let i = ref 0 in
 function () ->
  incr i;
  "x_" ^ string_of_int !i
;;

let mk_id id =
 let id = if id = "_" then fresh_name () else id in
  NotationPt.Ident (id,None)
;;

(*CSC: cut&paste from nCicReduction.split_prods, but does not check that
  the return type is a sort *)
let rec my_split_prods status ~subst context n te =
  match (n, NCicReduction.whd status ~subst context te) with
   | (0, _) -> context,te
   | (n, NCic.Prod (name,so,ta)) ->
       my_split_prods status ~subst ((name,(NCic.Decl so))::context) (n - 1) ta
   | (n, _) when n <= 0 -> context,te
   | (_, _) -> raise (Failure "my_split_prods")
;;

let mk_appl =
 function
    [] -> assert false
  | [x] -> x
  | NotationPt.Appl l1 :: l2 -> NotationPt.Appl (l1 @ l2)
  | l -> NotationPt.Appl l
;;

let mk_elim status uri leftno it (outsort,suffix) pragma =
 let _,ind_name,ty,cl = it in
 let srec_name = ind_name ^ "_" ^ suffix in
 let rec_name = mk_id srec_name in
 let name_of_k id = mk_id ("H_" ^ id) in
 let p_name = mk_id "Q_" in
 let params,ty = NCicReduction.split_prods status ~subst:[] [] leftno ty in
 let params = List.rev_map (function name,_ -> mk_id name) params in
 let args,sort = NCicReduction.split_prods status ~subst:[] [] (-1) ty in
 let args = List.rev_map (function name,_ -> mk_id name) args in
 let rec_arg = mk_id (fresh_name ()) in
 let mk_prods = 
  List.fold_right
   (fun name res -> NotationPt.Binder (`Forall,(name,None),res)) in
 let p_ty = mk_prods args
   (NotationPt.Binder
    (`Forall,
     (rec_arg,Some (mk_appl (mk_id ind_name :: params @ args))),
     NotationPt.Sort outsort)) in
 let mk_arrs n = mk_prods (HExtlib.mk_list (mk_id "_") n) in
 let args = args @ [rec_arg] in
 let k_names = List.map (function _,name,_ -> name_of_k name) cl in
 (*
 let final_params =
  List.map (function name -> name, None) params @
  [p_name,Some p_ty] @
  List.map (function name -> name, None) k_names @
  List.map (function name -> name, None) args in
 *)
 let cty = mk_appl (p_name :: args) in
 let ty = Some cty in
 let branches_with_args =
  List.map
   (function (_,name,ty) ->
     let _,ty = NCicReduction.split_prods status ~subst:[] [] leftno ty in
     let cargs,ty= my_split_prods status ~subst:[] [] (-1) ty in
     let cargs_recargs_nih =
      List.fold_left
       (fun (acc,nih) -> function
           _,NCic.Def _ -> assert false
         | name,NCic.Decl ty ->
            let context,ty = my_split_prods status ~subst:[] [] (-1) ty in
             match ty with
              | NCic.Const nref
              | NCic.Appl (NCic.Const nref::_)
                 when
                  let NReference.Ref (uri',_) = nref in
                   NUri.eq uri uri'
                 ->
                  let abs = List.rev_map (fun id,_ -> mk_id id) context in
                  let name = mk_id name in
                   (name, Some (
                   List.fold_right
                    (fun id res ->
                      NotationPt.Binder (`Lambda,(id,None),res))
                    abs
                    (NotationPt.Appl
                     (rec_name ::
                      params @
                      [p_name] @
                      k_names @
                      List.map (fun _ -> NotationPt.Implicit `JustOne)
                       (List.tl args) @
                      [mk_appl (name::abs)]))))::acc, nih + 1
              | _ -> (mk_id name,None)::acc,nih
       ) ([],0) cargs in
     let cargs_and_recursive_args, nih = cargs_recargs_nih in
     let cargs,recursive_args = List.split cargs_and_recursive_args in
     let recursive_args = HExtlib.filter_map (fun x -> x) recursive_args in
      (NotationPt.Pattern (name,None,List.map (fun x -> x,None) cargs),
       mk_appl (name_of_k name :: cargs @ recursive_args)), (name,cargs, nih)
   ) cl
 in
 let branches, branch_args = List.split branches_with_args in
 let bo = NotationPt.Case (rec_arg,Some (ind_name,None),Some p_name,branches) in
 let final_params =
  List.map (function name -> name, None) params @
  [p_name,Some p_ty] @
  List.map (function name, cargs, nih -> 
            name_of_k name, 
            Some (mk_prods cargs (mk_arrs nih 
             (mk_appl 
              (p_name::HExtlib.mk_list (NotationPt.Implicit `JustOne)
               (List.length args - 1) @
               [mk_appl (mk_id name :: params @ cargs)]))))) branch_args @
               List.map (function name -> name, None) args in
 let recno = List.length final_params in
 let where = recno - 1 in
 let attrs = `Generated, `Definition, pragma in
 let res =
  NotationPt.LetRec (`Inductive,
   [final_params, (rec_name,ty), bo, where], attrs)
 in
(*
  prerr_endline
   (BoxPp.render_to_string
     ~map_unicode_to_tex:false
     (function x::_ -> x | _ -> assert false)
     80 (NotationPres.render (fun _ -> None)
     (TermContentPres.pp_ast res)));
  prerr_endline "#####";
  let cobj = ("xxx", [], None, `Joint {
      Content.joint_id = "yyy";
      joint_kind = `Recursive [recno];
      joint_defs =
       [ `Definition {
            Content.def_name = Some srec_name;
            def_id = "zzz";
            def_aref = "www";
            def_term = bo;
            def_type = 
              List.fold_right 
                (fun x t -> NotationPt.Binder(`Forall,x,t))
                final_params cty
          }
       ];
    })
  in
  let ids_to_nrefs = Hashtbl.create 1 in
  let boxml = Content2pres.ncontent2pres ~ids_to_nrefs cobj in
  prerr_endline (
   (BoxPp.render_to_string ~map_unicode_to_tex:false
     (function x::_ -> x | _ -> assert false) 80 
     (NotationPres.mpres_of_box boxml)));
*)
  res
;;

let ast_of_sort s =
  let headrm prefix s =
    try 
      let len_prefix = String.length prefix in 
      assert (String.sub s 0 len_prefix = prefix);
      String.sub s len_prefix (String.length s - len_prefix)
    with Invalid_argument _ -> assert false
  in
  match s with
   | NCic.Prop -> `Prop,"ind"
   | NCic.Type []  -> `NType "", "rect_Type"
   | NCic.Type ((`Type,u) :: _) ->
       let name = NUri.name_of_uri u in
       `NType (headrm "Type" name), "rect_" ^ name
   | NCic.Type ((`CProp,u) :: _) ->
       let name = NUri.name_of_uri u in
       `NCProp (headrm "Type" name), 
       "rect_" ^ Str.replace_first (Str.regexp "Type") "CProp" name
   | _ -> assert false
;;

let mk_elims status (uri,_,_,_,obj) =
  match obj with
    NCic.Inductive (true,leftno,[itl],_) ->
      List.map (fun s-> mk_elim status uri leftno itl (ast_of_sort s) (`Elim s))
       (NCic.Prop::
         List.map (fun s -> NCic.Type s) (NCicEnvironment.get_universes ()))
   | _ -> []
;;

(********************* Projections **********************)

let mk_lambda =
 function
    [] -> assert false 
  | [t] -> t
  | l -> NotationPt.Appl l
;;

let rec count_prods = function NCic.Prod (_,_,t) -> 1 + count_prods t | _ -> 0;;

let rec nth_prod projs n ty =
 match ty with
    NCic.Prod (_,s,_) when n=0 -> projs, s
  | NCic.Prod (name,_,t) -> nth_prod (name::projs) (n-1) t
  | _ -> assert false
;;

(* this code should be unified with NTermCicContent.nast_of_cic0,
   but the two contexts have different types *)
let pp (status: #NCic.status) =
 let rec pp rels =
  function
    NCic.Rel i -> List.nth rels (i - 1)
  | NCic.Const _ as t -> NotationPt.NCic t
  | NCic.Sort s -> NotationPt.Sort (fst (ast_of_sort s))
  | NCic.Meta _
  | NCic.Implicit _ -> assert false
  | NCic.Appl l -> NotationPt.Appl (List.map (pp rels) l)
  | NCic.Prod (n,s,t) ->
     let n = mk_id n in
      NotationPt.Binder (`Pi, (n,Some (pp rels s)), pp (n::rels) t)
  | NCic.Lambda (n,s,t) ->
     let n = mk_id n in
      NotationPt.Binder (`Lambda, (n,Some (pp rels s)), pp (n::rels) t)
  | NCic.LetIn (n,ty,s,t) ->
     let n = mk_id n in
      NotationPt.LetIn ((n, Some (pp rels ty)), pp rels s, pp (n::rels) t)
  | NCic.Match (NReference.Ref (uri,_) as r,outty,te,patterns) ->
    let name = NUri.name_of_uri uri in
    let case_indty = Some (name, None) in
    let constructors, leftno =
     let _,leftno,tys,_,n = NCicEnvironment.get_checked_indtys status r in
     let _,_,_,cl  = List.nth tys n in
      cl,leftno
    in
    let rec eat_branch n rels ty pat =
      match (ty, pat) with
      | NCic.Prod (name, s, t), _ when n > 0 ->
         eat_branch (pred n) rels t pat
      | NCic.Prod (_, _, t), NCic.Lambda (name, s, t') ->
          let cv, rhs = eat_branch 0 ((mk_id name)::rels) t t' in
           (mk_id name, Some (pp rels s)) :: cv, rhs
      | _, _ -> [], pp rels pat
    in
    let patterns =
      try
        List.map2
          (fun (_, name, ty) pat ->
            let capture_variables,rhs = eat_branch leftno rels ty pat in
             NotationPt.Pattern (name, None, capture_variables), rhs
          ) constructors patterns
      with Invalid_argument _ -> assert false
    in
     NotationPt.Case (pp rels te, case_indty, Some (pp rels outty), patterns)
 in
  pp
;;

let mk_projection status leftno tyname consname consty (projname,_,_) i =
 let argsno = count_prods consty - leftno in
 let rec aux names ty leftno =
  match leftno,ty with
   | 0,_ ->
     let arg = mk_id "xxx" in
     let arg_ty = mk_appl (mk_id tyname :: List.rev names) in
     let bvar = mk_id "yyy" in
     let underscore = NotationPt.Ident ("_",None),None in
     let bvars =
      HExtlib.mk_list underscore i @ [bvar,None] @
       HExtlib.mk_list underscore (argsno - i -1) in
     let branch = NotationPt.Pattern (consname,None,bvars), bvar in
     let projs,outtype = nth_prod [] i ty in
     let rels =
      List.map
       (fun name -> mk_appl (mk_id name :: List.rev names @ [arg])) projs
      @ names in
     let outtype = pp status rels outtype in
     let outtype= NotationPt.Binder (`Lambda, (arg, Some arg_ty), outtype) in
      [arg, Some arg_ty], NotationPt.Case (arg,None,Some outtype,[branch])
   | _,NCic.Prod (name,_,t) ->
      let name = mk_id name in
      let params,body = aux (name::names) t (leftno - 1) in
       (name,None)::params, body
   | _,_ -> assert false
 in
 let params,bo = aux [] consty leftno in
 let pprojname = mk_id projname in
 let attrs = `Generated, `Definition, `Projection in
 let res =
  NotationPt.LetRec (`Inductive,
   [params, (pprojname,None), bo, leftno], attrs) in
(* prerr_endline
   (BoxPp.render_to_string
     ~map_unicode_to_tex:false
     (function x::_ -> x | _ -> assert false)
     80 (NotationPres.render (fun _ -> None)
     (TermContentPres.pp_ast res)));*)
   res
;;

let mk_projections status (_,_,_,_,obj) =
 match obj with
    NCic.Inductive
     (true,leftno,[_,tyname,_,[_,consname,consty]],(_,`Record fields))
    ->
     HExtlib.list_mapi (mk_projection status leftno tyname consname consty) fields
  | _ -> []
;;
