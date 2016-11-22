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

module P = Printf
module DT =  DisambiguateTypes
module Ast = NotationPt
module NRef = NReference 

let debug = ref false;;
let debug_print s = if !debug then prerr_endline (Lazy.force s);;

let cic_name_of_name = function
  | Ast.Ident (n, None) ->  n
  | _ -> assert false
;;

let rec mk_rels howmany from =
  match howmany with 
  | 0 -> []
  | _ -> (NCic.Rel (howmany + from)) :: (mk_rels (howmany-1) from)
;;

let refine_term (status: #NCicCoercion.status) metasenv subst context uri ~use_coercions term expty _
 ~localization_tbl
=
  assert (uri=None);
  debug_print (lazy (P.sprintf "TEST_INTERPRETATION: %s" 
    (status#ppterm ~metasenv ~subst ~context term)));
  try
    let localise t = 
      try NCicUntrusted.NCicHash.find localization_tbl t
      with Not_found -> 
        prerr_endline ("NOT LOCALISED" ^ status#ppterm ~metasenv ~subst ~context t);
        (*assert false*) HExtlib.dummy_floc
    in
    let metasenv, subst, term, _ = 
      NCicRefiner.typeof 
        (status#set_coerc_db 
          (if use_coercions then status#coerc_db else NCicCoercion.empty_db))
        metasenv subst context term expty ~localise 
    in
     Disambiguate.Ok (term, metasenv, subst, ())
  with
  | NCicRefiner.Uncertain loc_msg ->
      debug_print (lazy ("UNCERTAIN: [" ^ snd (Lazy.force loc_msg) ^ "] " ^ 
        status#ppterm ~metasenv ~subst ~context term)) ;
      Disambiguate.Uncertain loc_msg
  | NCicRefiner.RefineFailure loc_msg ->
      debug_print (lazy (P.sprintf "PRUNED:\nterm%s\nmessage:%s"
        (status#ppterm ~metasenv ~subst ~context term) (snd(Lazy.force loc_msg))));
      Disambiguate.Ko loc_msg
;;

let refine_obj status metasenv subst _context _uri ~use_coercions obj _ _ugraph
 ~localization_tbl 
=
  (*prerr_endline ((P.sprintf "TEST_INTERPRETATION: %s" (status#ppobj obj)));*)
  assert (metasenv=[]);
  assert (subst=[]);
  let localise t = 
    try NCicUntrusted.NCicHash.find localization_tbl t
    with Not_found -> 
      (*assert false*)HExtlib.dummy_floc
  in
  try
    let obj =
      NCicRefiner.typeof_obj
        (status#set_coerc_db
           (if use_coercions then status#coerc_db 
            else NCicCoercion.empty_db))
        obj ~localise 
    in
      Disambiguate.Ok (obj, [], [], ())
  with
  | NCicRefiner.Uncertain loc_msg ->
      debug_print (lazy ("UNCERTAIN: [" ^ snd (Lazy.force loc_msg) ^ "] " ^ 
        status#ppobj obj)) ;
      Disambiguate.Uncertain loc_msg
  | NCicRefiner.RefineFailure loc_msg ->
      debug_print (lazy (P.sprintf "PRUNED:\nobj: %s\nmessage: %s"
        (status#ppobj obj) (snd(Lazy.force loc_msg))));
      Disambiguate.Ko loc_msg
;;
  

  (* TODO move it to Cic *)
let find_in_context name context =
  let rec aux acc = function
    | [] -> raise Not_found
    | hd :: _ when hd = name -> acc
    | _ :: tl ->  aux (acc + 1) tl
  in
  aux 1 context

let interpretate_term_and_interpretate_term_option (status: #NCic.status)
  ?(create_dummy_ids=false) ~obj_context ~mk_choice ~env ~uri ~is_path
  ~localization_tbl 
=
  (* create_dummy_ids shouldbe used only for interpretating patterns *)
  assert (uri = None);

  let rec aux ~localize loc context = function
    | NotationPt.AttributedTerm (`Loc loc, term) ->
        let res = aux ~localize loc context term in
        if localize then 
         NCicUntrusted.NCicHash.add localization_tbl res loc;
       res
    | NotationPt.AttributedTerm (_, term) -> aux ~localize loc context term
    | NotationPt.Appl 
        (NotationPt.AttributedTerm (att, inner)::args)->
        aux ~localize loc context 
          (NotationPt.AttributedTerm (att,NotationPt.Appl (inner :: args)))
    | NotationPt.Appl (NotationPt.Appl inner :: args) ->
        aux ~localize loc context (NotationPt.Appl (inner @ args))
    | NotationPt.Appl (NotationPt.Symbol (symb, i) :: args) ->
        let cic_args = List.map (aux ~localize loc context) args in
        Disambiguate.resolve ~mk_choice ~env (DT.Symbol (symb, i)) (`Args cic_args)
    | NotationPt.Appl terms ->
       NCic.Appl (List.map (aux ~localize loc context) terms)
    | NotationPt.Binder (binder_kind, (var, typ), body) ->
        let cic_type = aux_option ~localize loc context `Type typ in
        let cic_name = cic_name_of_name var  in
        let cic_body = aux ~localize loc (cic_name :: context) body in
        (match binder_kind with
        | `Lambda -> NCic.Lambda (cic_name, cic_type, cic_body)
        | `Pi
        | `Forall -> NCic.Prod (cic_name, cic_type, cic_body)
        | `Exists ->
            Disambiguate.resolve ~env ~mk_choice (DT.Symbol ("exists", 0))
              (`Args [ cic_type; NCic.Lambda (cic_name, cic_type, cic_body) ]))
    | NotationPt.Case (term, indty_ident, outtype, branches) ->
        let cic_term = aux ~localize loc context term in
        let cic_outtype = aux_option ~localize loc context `Term outtype in
        let do_branch ((_, _, args), term) =
         let rec do_branch' context = function
           | [] -> aux ~localize loc context term
           | (name, typ) :: tl ->
               let cic_name = cic_name_of_name name in
               let cic_body = do_branch' (cic_name :: context) tl in
               let typ =
                 match typ with
                 | None -> NCic.Implicit `Type
                 | Some typ -> aux ~localize loc context typ
               in
               NCic.Lambda (cic_name, typ, cic_body)
         in
          do_branch' context args
        in
        if create_dummy_ids then
         let branches =
          List.map
           (function
               Ast.Wildcard,term -> ("wildcard",None,[]), term
             | Ast.Pattern _,_ ->
                raise (DisambiguateTypes.Invalid_choice 
                 (lazy (loc, "Syntax error: the left hand side of a "^
                   "branch pattern must be \"_\"")))
           ) branches in
         let indtype_ref =
          let uri = NUri.uri_of_string "cic:/matita/dummy/indty.ind" in 
          NRef.reference_of_spec uri (NRef.Ind (true,1,1))
         in
          NCic.Match (indtype_ref, cic_outtype, cic_term,
           (List.map do_branch branches))
        else
         let indtype_ref =
          match indty_ident with
          | Some (indty_ident, _) ->
             (match Disambiguate.resolve ~env ~mk_choice 
                (DT.Id indty_ident) (`Args []) with
              | NCic.Const (NRef.Ref (_,NRef.Ind _) as r) -> r
              | NCic.Implicit _ ->
                 raise (Disambiguate.Try_again 
                  (lazy "The type of the term to be matched is still unknown"))
              | t ->
                raise (DisambiguateTypes.Invalid_choice 
                  (lazy (loc,"The type of the term to be matched "^
                          "is not (co)inductive: " ^ status#ppterm 
                          ~metasenv:[] ~subst:[] ~context:[] t))))
          | None ->
              let rec fst_constructor =
                function
                   (Ast.Pattern (head, _, _), _) :: _ -> head
                 | (Ast.Wildcard, _) :: tl -> fst_constructor tl
                 | [] -> raise (DT.Invalid_choice (lazy (loc,"The type "^
                     "of the term to be matched cannot be determined "^
                     "because it is an inductive type without constructors "^
                     "or because all patterns use wildcards")))
              in
(*
              DisambiguateTypes.Environment.iter
                  (fun k v ->
                      prerr_endline
                        (DisambiguateTypes.string_of_domain_item k ^ " => " ^
                        description_of_alias v)) env; 
*)
              (match Disambiguate.resolve ~env ~mk_choice
                (DT.Id (fst_constructor branches)) (`Args []) with
              | NCic.Const (NRef.Ref (_,NRef.Con _) as r) -> 
                   let b,_,_,_,_= NCicEnvironment.get_checked_indtys status r in
                   NRef.mk_indty b r
              | NCic.Implicit _ ->
                 raise (Disambiguate.Try_again 
                  (lazy "The type of the term to be matched is still unknown"))
              | t ->
                raise (DisambiguateTypes.Invalid_choice 
                  (lazy (loc, 
                  "The type of the term to be matched is not (co)inductive: " 
                  ^ status#ppterm ~metasenv:[] ~subst:[] ~context:[] t))))
         in
         let _,leftsno,itl,_,indtyp_no =
          NCicEnvironment.get_checked_indtys status indtype_ref in
         let _,_,_,cl =
          try
           List.nth itl indtyp_no
          with _ -> assert false in
         let rec count_prod t =
                 match NCicReduction.whd status ~subst:[] [] t with
               NCic.Prod (_, _, t) -> 1 + (count_prod t)
             | _ -> 0 
         in 
         let rec sort branches cl =
          match cl with
             [] ->
              let rec analyze unused unrecognized useless =
               function
                  [] ->
                   if unrecognized != [] then
                    raise (DisambiguateTypes.Invalid_choice
                     (lazy
                       (loc,"Unrecognized constructors: " ^
                        String.concat " " unrecognized)))
                   else if useless > 0 then
                    raise (DisambiguateTypes.Invalid_choice
                     (lazy
                       (loc,"The last " ^ string_of_int useless ^
                        "case" ^ if useless > 1 then "s are" else " is" ^
                        " unused")))
                   else
                    []
                | (Ast.Wildcard,_)::tl when not unused ->
                    analyze true unrecognized useless tl
                | (Ast.Pattern (head,_,_),_)::tl when not unused ->
                    analyze unused (head::unrecognized) useless tl
                | _::tl -> analyze unused unrecognized (useless + 1) tl
              in
               analyze false [] 0 branches
           | (_,name,ty)::cltl ->
              let rec find_and_remove =
               function
                  [] ->
                   raise
                    (DisambiguateTypes.Invalid_choice
                     (lazy (loc, "Missing case: " ^ name)))
                | ((Ast.Wildcard, _) as branch :: _) as branches ->
                    branch, branches
                | (Ast.Pattern (name',_,_),_) as branch :: tl
                   when name = name' ->
                    branch,tl
                | branch::tl ->
                   let found,rest = find_and_remove tl in
                    found, branch::rest
              in
               let branch,tl = find_and_remove branches in
               match branch with
                  Ast.Pattern (name,y,args),term ->
                   if List.length args = count_prod ty - leftsno then
                    ((name,y,args),term)::sort tl cltl
                   else
                    raise
                     (DisambiguateTypes.Invalid_choice
                      (lazy (loc,"Wrong number of arguments for " ^ name)))
                | Ast.Wildcard,term ->
                   let rec mk_lambdas =
                    function
                       0 -> term
                     | n ->
                        NotationPt.Binder
                         (`Lambda, (NotationPt.Ident ("_", None), None),
                           mk_lambdas (n - 1))
                   in
                    (("wildcard",None,[]),
                     mk_lambdas (count_prod ty - leftsno)) :: sort tl cltl
         in
          let branches = sort branches cl in
           NCic.Match (indtype_ref, cic_outtype, cic_term,
            (List.map do_branch branches))
    | NotationPt.Cast (t1, t2) ->
        let cic_t1 = aux ~localize loc context t1 in
        let cic_t2 = aux ~localize loc context t2 in
        NCic.LetIn ("_",cic_t2,cic_t1, NCic.Rel 1)
    | NotationPt.LetIn ((name, typ), def, body) ->
        let cic_def = aux ~localize loc context def in
        let cic_name = cic_name_of_name name in
        let cic_typ =
          match typ with
          | None -> NCic.Implicit `Type
          | Some t -> aux ~localize loc context t
        in
        let cic_body = aux ~localize loc (cic_name :: context) body in
        NCic.LetIn (cic_name, cic_typ, cic_def, cic_body)
    | NotationPt.Ident _
    | NotationPt.Uri _
    | NotationPt.NRef _ when is_path -> raise Disambiguate.PathNotWellFormed
    | NotationPt.Ident (name, subst) ->
       assert (subst = None);
       (try
             NCic.Rel (find_in_context name context)
       with Not_found -> 
         try NCic.Const (List.assoc name obj_context)
         with Not_found ->
            Disambiguate.resolve ~env ~mk_choice (DT.Id name) (`Args []))
    | NotationPt.Uri (uri, subst) ->
       assert (subst = None);
       (try
         NCic.Const (NRef.reference_of_string uri)
        with NRef.IllFormedReference _ ->
         NotationPt.fail loc "Ill formed reference")
    | NotationPt.NRef nref -> NCic.Const nref
    | NotationPt.NCic t ->  t
    | NotationPt.Implicit `Vector -> NCic.Implicit `Vector
    | NotationPt.Implicit `JustOne -> NCic.Implicit `Term
    | NotationPt.Implicit (`Tagged s) -> NCic.Implicit (`Tagged s)
    | NotationPt.UserInput -> NCic.Implicit `Hole
    | NotationPt.Num (num, i) -> 
        Disambiguate.resolve ~env ~mk_choice (DT.Num i) (`Num_arg num)
    | NotationPt.Meta (index, subst) ->
        let cic_subst =
         List.map
          (function None -> assert false| Some t -> aux ~localize loc context t)
          subst
        in
         NCic.Meta (index, (0, NCic.Ctx cic_subst))
    | NotationPt.Sort `Prop -> NCic.Sort NCic.Prop
    | NotationPt.Sort `Set -> NCic.Sort (NCic.Type
       [`Type,NUri.uri_of_string "cic:/matita/pts/Type.univ"])
    | NotationPt.Sort (`NType s) -> NCic.Sort (NCic.Type
       [`Type,NUri.uri_of_string ("cic:/matita/pts/Type" ^ s ^ ".univ")])
    | NotationPt.Sort (`NCProp s) -> NCic.Sort (NCic.Type
       [`CProp,NUri.uri_of_string ("cic:/matita/pts/Type" ^ s ^ ".univ")])
    | NotationPt.Symbol (symbol, instance) ->
        Disambiguate.resolve ~env ~mk_choice 
         (DT.Symbol (symbol, instance)) (`Args [])
    | NotationPt.Variable _
    | NotationPt.Magic _
    | NotationPt.Layout _
    | NotationPt.Literal _ -> assert false (* god bless Bologna *)
  and aux_option ~localize loc context annotation = function
    | None -> NCic.Implicit annotation
    | Some (NotationPt.AttributedTerm (`Loc loc, term)) ->
        let res = aux_option ~localize loc context annotation (Some term) in
        if localize then 
          NCicUntrusted.NCicHash.add localization_tbl res loc;
        res
    | Some (NotationPt.AttributedTerm (_, term)) ->
        aux_option ~localize loc context annotation (Some term)
    | Some NotationPt.Implicit `JustOne -> NCic.Implicit annotation
    | Some NotationPt.Implicit `Vector -> NCic.Implicit `Vector
    | Some term -> aux ~localize loc context term
  in
   (fun ~context -> aux ~localize:true HExtlib.dummy_floc context),
   (fun ~context -> aux_option ~localize:true HExtlib.dummy_floc context)
;;

let interpretate_term status ?(create_dummy_ids=false) ~context ~env ~uri
 ~is_path ast ~obj_context ~localization_tbl ~mk_choice
=
  let context = List.map fst context in
  fst 
    (interpretate_term_and_interpretate_term_option status
      ~obj_context ~mk_choice ~create_dummy_ids ~env ~uri ~is_path
      ~localization_tbl)
    ~context ast
;;

let interpretate_term_option status ?(create_dummy_ids=false) ~context ~env ~uri
 ~is_path ~localization_tbl ~mk_choice ~obj_context
=
  let context = List.map fst context in
  snd 
    (interpretate_term_and_interpretate_term_option status
      ~obj_context ~mk_choice ~create_dummy_ids ~env ~uri ~is_path
      ~localization_tbl)
    ~context 
;;

let disambiguate_path status path =
  let localization_tbl = NCicUntrusted.NCicHash.create 23 in
  fst
    (interpretate_term_and_interpretate_term_option status
    ~obj_context:[] ~mk_choice:(fun _ -> assert false)
    ~create_dummy_ids:true ~env:DisambiguateTypes.Environment.empty
    ~uri:None ~is_path:true ~localization_tbl) ~context:[] path
;;

let ncic_name_of_ident = function
  | Ast.Ident (name, None) -> name
  | _ -> assert false
;;

let interpretate_obj status
(*      ?(create_dummy_ids=false)  *)
     ~context ~env ~uri ~is_path obj ~localization_tbl ~mk_choice 
=
 assert (context = []);
 assert (is_path = false);
 let interpretate_term ~obj_context =
  interpretate_term ~mk_choice ~localization_tbl ~obj_context in
 let interpretate_term_option ~obj_context =
   interpretate_term_option ~mk_choice ~localization_tbl ~obj_context in
 let uri = match uri with | None -> assert false | Some u -> u in
 match obj with
 | NotationPt.Theorem (name, ty, bo, attrs) ->
     let _, flavour, _ = attrs in
     let ty' = 
       interpretate_term status
         ~obj_context:[] ~context:[] ~env ~uri:None ~is_path:false ty 
     in
     let height = (* XXX calculate *) 0 in
     uri, height, [], [], 
     (match bo,flavour with
      | None,`Axiom -> 
          NCic.Constant ([],name,None,ty',attrs)
      | Some _,`Axiom -> assert false
      | None,_ ->
          NCic.Constant ([],name,Some (NCic.Implicit `Term),ty',attrs)
      | Some bo,_ ->
          let bo = 
            interpretate_term status
             ~obj_context:[] ~context:[] ~env ~uri:None ~is_path:false bo
          in
          NCic.Constant ([],name,Some bo,ty',attrs))
 | NotationPt.Inductive (params,tyl,source) ->
    let context,params =
     let context,res =
      List.fold_left
       (fun (context,res) (name,t) ->
         let t =
          match t with
             None -> NotationPt.Implicit `JustOne
           | Some t -> t in
         let name = cic_name_of_name name in
         let t =
          interpretate_term status ~obj_context:[] ~context ~env ~uri:None
           ~is_path:false t
         in
          (name,NCic.Decl t)::context,(name,t)::res
       ) ([],[]) params
     in
      context,List.rev res in
    let add_params =
     List.fold_right (fun (name,ty) t -> NCic.Prod (name,ty,t)) params in
    let leftno = List.length params in
    let _,inductive,_,_ = try List.hd tyl with Failure _ -> assert false in
    let obj_context =
     snd (
      List.fold_left
       (fun (i,res) (name,_,_,_) ->
         let nref =
          NRef.reference_of_spec uri (NRef.Ind (inductive,i,leftno))
         in
          i+1,(name,nref)::res)
       (0,[]) tyl) in
    let tyl =
     List.map
      (fun (name,_,ty,cl) ->
        let ty' =
         add_params
         (interpretate_term status ~obj_context:[] ~context ~env ~uri:None
           ~is_path:false ty) in
        let cl' =
         List.map
          (fun (name,ty) ->
            let ty' =
             add_params
              (interpretate_term status ~obj_context ~context ~env ~uri:None
                ~is_path:false ty) in
            let relevance = [] in
             relevance,name,ty'
          ) cl in
        let relevance = [] in
         relevance,name,ty',cl'
      ) tyl
    in
     let height = (* XXX calculate *) 0 in
     let attrs = source, `Regular in
     uri, height, [], [], 
     NCic.Inductive (inductive,leftno,tyl,attrs)
 | NotationPt.Record (params,name,ty,fields,source) ->
    let context,params =
     let context,res =
      List.fold_left
       (fun (context,res) (name,t) ->
         let t =
          match t with
             None -> NotationPt.Implicit `JustOne
           | Some t -> t in
         let name = cic_name_of_name name in
         let t =
          interpretate_term status ~obj_context:[] ~context ~env ~uri:None
           ~is_path:false t
         in
          (name,NCic.Decl t)::context,(name,t)::res
       ) ([],[]) params
     in
      context,List.rev res in
    let add_params =
     List.fold_right (fun (name,ty) t -> NCic.Prod (name,ty,t)) params in
    let leftno = List.length params in
    let ty' =
     add_params
      (interpretate_term status ~obj_context:[] ~context ~env ~uri:None
        ~is_path:false ty) in
    let nref =
     NRef.reference_of_spec uri (NRef.Ind (true,0,leftno)) in
    let obj_context = [name,nref] in
    let fields' =
     snd (
      List.fold_left
       (fun (context,res) (name,ty,_coercion,_arity) ->
         let ty =
          interpretate_term status ~obj_context ~context ~env ~uri:None
           ~is_path:false ty in
         let context' = (name,NCic.Decl ty)::context in
          context',(name,ty)::res
       ) (context,[]) fields) in
    let concl =
     let mutind = NCic.Const nref in
     if params = [] then mutind
     else
      NCic.Appl
       (mutind::mk_rels (List.length params) (List.length fields)) in
    let con =
     List.fold_left (fun t (name,ty) -> NCic.Prod (name,ty,t)) concl fields' in
    let con' = add_params con in
    let relevance = [] in
    let tyl = [relevance,name,ty',[relevance,"mk_" ^ name,con']] in
    let field_names = List.map (fun (x,_,y,z) -> x,y,z) fields in
     let height = (* XXX calculate *) 0 in
     let attrs = source, `Record field_names in
     uri, height, [], [], 
     NCic.Inductive (true,leftno,tyl,attrs)
 | NotationPt.LetRec (kind, defs, attrs) ->
     let inductive = kind = `Inductive in
     let _,obj_context =
       List.fold_left
         (fun (i,acc) (_,(name,_),_,k) -> 
          (i+1, 
            (ncic_name_of_ident name, NRef.reference_of_spec uri 
             (if inductive then NRef.Fix (i,k,0)
              else NRef.CoFix i)) :: acc))
         (0,[]) defs
     in
     let inductiveFuns =
       List.map
         (fun (params, (name, typ), body, decr_idx) ->
           let add_binders kind t =
            List.fold_right
             (fun var t -> 
                NotationPt.Binder (kind, var, t)) params t
           in
           let cic_body =
             interpretate_term status
               ~obj_context ~context ~env ~uri:None ~is_path:false
               (add_binders `Lambda body) 
           in
           let cic_type =
             interpretate_term_option status
               ~obj_context:[]
               ~context ~env ~uri:None ~is_path:false `Type
               (HExtlib.map_option (add_binders `Pi) typ)
           in
           ([],ncic_name_of_ident name, decr_idx, cic_type, cic_body))
         defs
     in
     let height = (* XXX calculate *) 0 in
     uri, height, [], [], 
     NCic.Fixpoint (inductive,inductiveFuns,attrs)
;;

let disambiguate_term (status: #NCicCoercion.status) ~context ~metasenv ~subst
 ~expty ~mk_implicit ~description_of_alias ~fix_instance ~mk_choice
 ~aliases ~universe ~lookup_in_library (text,prefix_len,term) 
=
  let mk_localization_tbl x = NCicUntrusted.NCicHash.create x in
   let res,b =
    MultiPassDisambiguator.disambiguate_thing
     ~freshen_thing:NotationUtil.freshen_term
     ~context ~metasenv ~initial_ugraph:() ~aliases
     ~mk_implicit ~description_of_alias ~fix_instance
     ~string_context_of_context:(List.map (fun (x,_) -> Some x))
     ~universe ~uri:None ~pp_thing:(NotationPp.pp_term status)
     ~passes:(MultiPassDisambiguator.passes ())
     ~lookup_in_library ~domain_of_thing:Disambiguate.domain_of_term
     ~interpretate_thing:(interpretate_term status ~obj_context:[] ~mk_choice (?create_dummy_ids:None))
     ~refine_thing:(refine_term status) (text,prefix_len,term)
     ~mk_localization_tbl ~expty ~subst
   in
    List.map (function (a,b,c,d,_) -> a,b,c,d) res, b
;;

let disambiguate_obj (status: #NCicCoercion.status)
   ~mk_implicit ~description_of_alias ~fix_instance ~mk_choice
   ~aliases ~universe ~lookup_in_library ~uri (text,prefix_len,obj) 
 =
  let mk_localization_tbl x = NCicUntrusted.NCicHash.create x in
   let res,b =
    MultiPassDisambiguator.disambiguate_thing
     ~freshen_thing:NotationUtil.freshen_obj
     ~context:[] ~metasenv:[] ~subst:[] ~initial_ugraph:() ~aliases
     ~mk_implicit ~description_of_alias ~fix_instance
     ~string_context_of_context:(List.map (fun (x,_) -> Some x))
     ~universe 
     ~uri:(Some uri)
     ~pp_thing:(NotationPp.pp_obj (NotationPp.pp_term status))
     ~passes:(MultiPassDisambiguator.passes ())
     ~lookup_in_library ~domain_of_thing:Disambiguate.domain_of_obj
     ~interpretate_thing:(interpretate_obj status ~mk_choice)
     ~refine_thing:(refine_obj status) 
     (text,prefix_len,obj)
     ~mk_localization_tbl ~expty:`XTNone
   in
    List.map (function (a,b,c,d,_) -> a,b,c,d) res, b
;;
(*
let _ = 
let mk_type n = 
  if n = 0 then
     [false, NUri.uri_of_string ("cic:/matita/pts/Type.univ")]
  else
     [false, NUri.uri_of_string ("cic:/matita/pts/Type"^string_of_int n^".univ")]
in
let mk_cprop n = 
  if n = 0 then 
    [false, NUri.uri_of_string ("cic:/matita/pts/CProp.univ")]
  else
    [false, NUri.uri_of_string ("cic:/matita/pts/CProp"^string_of_int n^".univ")]
in
         NCicEnvironment.add_constraint true (mk_type 0) (mk_type 1);
         NCicEnvironment.add_constraint true (mk_cprop 0) (mk_cprop 1);
         NCicEnvironment.add_constraint true (mk_cprop 0) (mk_type 1);
         NCicEnvironment.add_constraint true (mk_type 0) (mk_cprop 1);
         NCicEnvironment.add_constraint false (mk_cprop 0) (mk_type 0);
         NCicEnvironment.add_constraint false (mk_type 0) (mk_cprop 0);

         NCicEnvironment.add_constraint true (mk_type 1) (mk_type 2);
         NCicEnvironment.add_constraint true (mk_cprop 1) (mk_cprop 2);
         NCicEnvironment.add_constraint true (mk_cprop 1) (mk_type 2);
         NCicEnvironment.add_constraint true (mk_type 1) (mk_cprop 2);
         NCicEnvironment.add_constraint false (mk_cprop 1) (mk_type 1);
         NCicEnvironment.add_constraint false (mk_type 1) (mk_cprop 1);

         NCicEnvironment.add_constraint true (mk_type 2) (mk_type 3);
         NCicEnvironment.add_constraint true (mk_cprop 2) (mk_cprop 3);
         NCicEnvironment.add_constraint true (mk_cprop 2) (mk_type 3);
         NCicEnvironment.add_constraint true (mk_type 2) (mk_cprop 3);
         NCicEnvironment.add_constraint false (mk_cprop 2) (mk_type 2);
         NCicEnvironment.add_constraint false (mk_type 2) (mk_cprop 2);

         NCicEnvironment.add_constraint false (mk_cprop 3) (mk_type 3);
         NCicEnvironment.add_constraint false (mk_type 3) (mk_cprop 3);

;;
*)

