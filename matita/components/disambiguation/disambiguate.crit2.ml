(* Copyright (C) 2004, HELM Team.
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
 * http://helm.cs.unibo.it/
 *)

(* $Id: disambiguate.ml 7760 2007-10-26 12:37:21Z sacerdot $ *)

open Printf

open DisambiguateTypes
open UriManager

module Ast = CicNotationPt

(* the integer is an offset to be added to each location *)
exception NoWellTypedInterpretation of
 int *
 ((Stdpp.location list * string * string) list *
  (DisambiguateTypes.domain_item * DisambiguateTypes.codomain_item) list *
  Stdpp.location option * string Lazy.t * bool) list
exception PathNotWellFormed

  (** raised when an environment is not enough informative to decide *)
exception Try_again of string Lazy.t

type aliases = bool * DisambiguateTypes.environment
type 'a disambiguator_input = string * int * 'a

type domain = domain_tree list
and domain_tree = Node of Stdpp.location list * domain_item * domain

let rec string_of_domain =
 function
    [] -> ""
  | Node (_,domain_item,l)::tl ->
     DisambiguateTypes.string_of_domain_item domain_item ^
      " [ " ^ string_of_domain l ^ " ] " ^ string_of_domain tl

let rec filter_map_domain f =
 function
    [] -> []
  | Node (locs,domain_item,l)::tl ->
     match f locs domain_item with
        None -> filter_map_domain f l @ filter_map_domain f tl
      | Some res -> res :: filter_map_domain f l @ filter_map_domain f tl

let rec map_domain f =
 function
    [] -> []
  | Node (locs,domain_item,l)::tl ->
     f locs domain_item :: map_domain f l @ map_domain f tl

let uniq_domain dom =
 let rec aux seen =
  function
     [] -> seen,[]
   | Node (locs,domain_item,l)::tl ->
      if List.mem domain_item seen then
       let seen,l = aux seen l in
       let seen,tl = aux seen tl in
        seen, l @ tl
      else
       let seen,l = aux (domain_item::seen) l in
       let seen,tl = aux seen tl in
        seen, Node (locs,domain_item,l)::tl
 in
  snd (aux [] dom)

let debug = false
let debug_print s = if debug then prerr_endline (Lazy.force s) else ()

(*
  (** print benchmark information *)
let benchmark = true
let max_refinements = ref 0       (* benchmarking is not thread safe *)
let actual_refinements = ref 0
let domain_size = ref 0
let choices_avg = ref 0.
*)

let descr_of_domain_item = function
 | Id s -> s
 | Symbol (s, _) -> s
 | Num i -> string_of_int i

type 'a test_result =
  | Ok of 'a * Cic.metasenv
  | Ko of Stdpp.location option * string Lazy.t
  | Uncertain of Stdpp.location option * string Lazy.t

let refine_term metasenv context uri term ugraph ~localization_tbl =
(*   if benchmark then incr actual_refinements; *)
  assert (uri=None);
    debug_print (lazy (sprintf "TEST_INTERPRETATION: %s" (CicPp.ppterm term)));
    try
      let term', _, metasenv',ugraph1 = 
	CicRefine.type_of_aux' metasenv context term ugraph ~localization_tbl in
        debug_print (lazy (sprintf "OK!!!"));
	(Ok (term', metasenv')),ugraph1
    with
     exn ->
      let rec process_exn loc =
       function
          HExtlib.Localized (loc,exn) -> process_exn (Some loc) exn
        | CicRefine.Uncertain msg ->
            debug_print (lazy ("UNCERTAIN!!! [" ^ (Lazy.force msg) ^ "] " ^ CicPp.ppterm term)) ;
            Uncertain (loc,msg),ugraph
        | CicRefine.RefineFailure msg ->
            debug_print (lazy (sprintf "PRUNED!!!\nterm%s\nmessage:%s"
              (CicPp.ppterm term) (Lazy.force msg)));
            Ko (loc,msg),ugraph
       | exn -> raise exn
      in
       process_exn None exn

let refine_obj metasenv context uri obj ugraph ~localization_tbl =
 assert (context = []);
   debug_print (lazy (sprintf "TEST_INTERPRETATION: %s" (CicPp.ppobj obj))) ;
   try
     let obj', metasenv,ugraph =
      CicRefine.typecheck metasenv uri obj ~localization_tbl
     in
       debug_print (lazy (sprintf "OK!!!"));
       (Ok (obj', metasenv)),ugraph
   with
     exn ->
      let rec process_exn loc =
       function
          HExtlib.Localized (loc,exn) -> process_exn (Some loc) exn
        | CicRefine.Uncertain msg ->
            debug_print (lazy ("UNCERTAIN!!! [" ^ (Lazy.force msg) ^ "] " ^ CicPp.ppobj obj)) ;
            Uncertain (loc,msg),ugraph
        | CicRefine.RefineFailure msg ->
            debug_print (lazy (sprintf "PRUNED!!!\nterm%s\nmessage:%s"
              (CicPp.ppobj obj) (Lazy.force msg))) ;
            Ko (loc,msg),ugraph
       | exn -> raise exn
      in
       process_exn None exn

let resolve (env: codomain_item Environment.t) (item: domain_item) ?(num = "") ?(args = []) () =
  try
    snd (Environment.find item env) env num args
  with Not_found -> 
    failwith ("Domain item not found: " ^ 
      (DisambiguateTypes.string_of_domain_item item))

  (* TODO move it to Cic *)
let find_in_context name context =
  let rec aux acc = function
    | [] -> raise Not_found
    | Cic.Name hd :: tl when hd = name -> acc
    | _ :: tl ->  aux (acc + 1) tl
  in
  aux 1 context

let interpretate_term ?(create_dummy_ids=false) ~(context: Cic.name list) ~env ~uri ~is_path ast
     ~localization_tbl
=
  (* create_dummy_ids shouldbe used only for interpretating patterns *)
  assert (uri = None);
  let rec aux ~localize loc (context: Cic.name list) = function
    | CicNotationPt.AttributedTerm (`Loc loc, term) ->
        let res = aux ~localize loc context term in
         if localize then Cic.CicHash.add localization_tbl res loc;
         res
    | CicNotationPt.AttributedTerm (_, term) -> aux ~localize loc context term
    | CicNotationPt.Appl (CicNotationPt.Symbol (symb, i) :: args) ->
        let cic_args = List.map (aux ~localize loc context) args in
        resolve env (Symbol (symb, i)) ~args:cic_args ()
    | CicNotationPt.Appl terms ->
       Cic.Appl (List.map (aux ~localize loc context) terms)
    | CicNotationPt.Binder (binder_kind, (var, typ), body) ->
        let cic_type = aux_option ~localize loc context (Some `Type) typ in
        let cic_name = CicNotationUtil.cic_name_of_name var in
        let cic_body = aux ~localize loc (cic_name :: context) body in
        (match binder_kind with
        | `Lambda -> Cic.Lambda (cic_name, cic_type, cic_body)
        | `Pi
        | `Forall -> Cic.Prod (cic_name, cic_type, cic_body)
        | `Exists ->
            resolve env (Symbol ("exists", 0))
              ~args:[ cic_type; Cic.Lambda (cic_name, cic_type, cic_body) ] ())
    | CicNotationPt.Case (term, indty_ident, outtype, branches) ->
        let cic_term = aux ~localize loc context term in
        let cic_outtype = aux_option ~localize loc context None outtype in
        let do_branch ((head, _, args), term) =
         let rec do_branch' context = function
           | [] -> aux ~localize loc context term
           | (name, typ) :: tl ->
               let cic_name = CicNotationUtil.cic_name_of_name name in
               let cic_body = do_branch' (cic_name :: context) tl in
               let typ =
                 match typ with
                 | None -> Cic.Implicit (Some `Type)
                 | Some typ -> aux ~localize loc context typ
               in
               Cic.Lambda (cic_name, typ, cic_body)
         in
          do_branch' context args
        in
        let indtype_uri, indtype_no =
          if create_dummy_ids then
            (UriManager.uri_of_string "cic:/fake_indty.con", 0)
          else
          match indty_ident with
          | Some (indty_ident, _) ->
             (match resolve env (Id indty_ident) () with
              | Cic.MutInd (uri, tyno, _) -> (uri, tyno)
              | Cic.Implicit _ ->
                 raise (Try_again (lazy "The type of the term to be matched
                  is still unknown"))
              | _ ->
                raise (Invalid_choice (Some loc, lazy "The type of the term to be matched is not (co)inductive!")))
          | None ->
              let rec fst_constructor =
                function
                   (Ast.Pattern (head, _, _), _) :: _ -> head
                 | (Ast.Wildcard, _) :: tl -> fst_constructor tl
                 | [] -> raise (Invalid_choice (Some loc, lazy "The type of the term to be matched cannot be determined because it is an inductive type without constructors or because all patterns use wildcards"))
              in
              (match resolve env (Id (fst_constructor branches)) () with
              | Cic.MutConstruct (indtype_uri, indtype_no, _, _) ->
                  (indtype_uri, indtype_no)
              | Cic.Implicit _ ->
                 raise (Try_again (lazy "The type of the term to be matched
                  is still unknown"))
              | _ ->
                raise (Invalid_choice (Some loc, lazy "The type of the term to be matched is not (co)inductive!")))
        in
        let branches =
         if create_dummy_ids then
          List.map
           (function
               Ast.Wildcard,term -> ("wildcard",None,[]), term
             | Ast.Pattern _,_ ->
                raise (Invalid_choice (Some loc, lazy "Syntax error: the left hand side of a branch patterns must be \"_\""))
           ) branches
         else
         match fst(CicEnvironment.get_obj CicUniv.empty_ugraph indtype_uri) with
            Cic.InductiveDefinition (il,_,leftsno,_) ->
             let _,_,_,cl =
              try
               List.nth il indtype_no
              with _ -> assert false
             in
              let rec count_prod t =
                match CicReduction.whd [] t with
                    Cic.Prod (_, _, t) -> 1 + (count_prod t)
                  | _ -> 0 
              in 
              let rec sort branches cl =
               match cl with
                  [] ->
                   let rec analyze unused unrecognized useless =
                    function
                       [] ->
                        if unrecognized != [] then
                         raise (Invalid_choice
                          (Some loc,
                           lazy
                            ("Unrecognized constructors: " ^
                             String.concat " " unrecognized)))
                        else if useless > 0 then
                         raise (Invalid_choice
                          (Some loc,
                           lazy
                            ("The last " ^ string_of_int useless ^
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
                | (name,ty)::cltl ->
                   let rec find_and_remove =
                    function
                       [] ->
                        raise
                         (Invalid_choice
                          (Some loc, lazy ("Missing case: " ^ name)))
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
                          (Invalid_choice
                           (Some loc,
                             lazy ("Wrong number of arguments for " ^ name)))
                     | Ast.Wildcard,term ->
                        let rec mk_lambdas =
                         function
                            0 -> term
                          | n ->
                             CicNotationPt.Binder
                              (`Lambda, (CicNotationPt.Ident ("_", None), None),
                                mk_lambdas (n - 1))
                        in
                         (("wildcard",None,[]),
                          mk_lambdas (count_prod ty - leftsno)) :: sort tl cltl
              in
               sort branches cl
          | _ -> assert false
        in
        Cic.MutCase (indtype_uri, indtype_no, cic_outtype, cic_term,
          (List.map do_branch branches))
    | CicNotationPt.Cast (t1, t2) ->
        let cic_t1 = aux ~localize loc context t1 in
        let cic_t2 = aux ~localize loc context t2 in
        Cic.Cast (cic_t1, cic_t2)
    | CicNotationPt.LetIn ((name, typ), def, body) ->
        let cic_def = aux ~localize loc context def in
        let cic_name = CicNotationUtil.cic_name_of_name name in
        let cic_def =
          match typ with
          | None -> cic_def
          | Some t -> Cic.Cast (cic_def, aux ~localize loc context t)
        in
        let cic_body = aux ~localize loc (cic_name :: context) body in
        Cic.LetIn (cic_name, cic_def, cic_body)
    | CicNotationPt.LetRec (kind, defs, body) ->
        let context' =
          List.fold_left
            (fun acc (_, (name, _), _, _) ->
              CicNotationUtil.cic_name_of_name name :: acc)
            context defs
        in
        let cic_body =
         let unlocalized_body = aux ~localize:false loc context' body in
         match unlocalized_body with
            Cic.Rel n when n <= List.length defs -> `AvoidLetInNoAppl n
          | Cic.Appl (Cic.Rel n::l) when n <= List.length defs ->
             (try
               let l' =
                List.map
                 (function t ->
                   let t',subst,metasenv =
                    CicMetaSubst.delift_rels [] [] (List.length defs) t
                   in
                    assert (subst=[]);
                    assert (metasenv=[]);
                    t') l
               in
                (* We can avoid the LetIn. But maybe we need to recompute l'
                   so that it is localized *)
                if localize then
                 match body with
                    CicNotationPt.AttributedTerm (_,CicNotationPt.Appl(_::l)) ->
                     let l' = List.map (aux ~localize loc context) l in
                      `AvoidLetIn (n,l')
                  | _ -> assert false
                else
                 `AvoidLetIn (n,l')
              with
               CicMetaSubst.DeliftingARelWouldCaptureAFreeVariable ->
                if localize then
                 `AddLetIn (aux ~localize loc context' body)
                else
                 `AddLetIn unlocalized_body)
          | _ ->
             if localize then
              `AddLetIn (aux ~localize loc context' body)
             else
              `AddLetIn unlocalized_body
        in
        let inductiveFuns =
          List.map
            (fun (params, (name, typ), body, decr_idx) ->
              let add_binders kind t =
               List.fold_right
                (fun var t -> CicNotationPt.Binder (kind, var, t)) params t
              in
              let cic_body =
               aux ~localize loc context' (add_binders `Lambda body) in
              let cic_type =
               aux_option ~localize loc context (Some `Type)
                (HExtlib.map_option (add_binders `Pi) typ) in
              let name =
                match CicNotationUtil.cic_name_of_name name with
                | Cic.Anonymous ->
                    CicNotationPt.fail loc
                      "Recursive functions cannot be anonymous"
                | Cic.Name name -> name
              in
              (name, decr_idx, cic_type, cic_body))
            defs
        in
        let fix_or_cofix n =
         match kind with
            `Inductive -> Cic.Fix (n,inductiveFuns)
          | `CoInductive ->
              let coinductiveFuns =
                List.map
                 (fun (name, _, typ, body) -> name, typ, body)
                 inductiveFuns
              in
               Cic.CoFix (n,coinductiveFuns)
        in
         let counter = ref ~-1 in
         let build_term funs (var,_,_,_) t =
          incr counter;
          Cic.LetIn (Cic.Name var, fix_or_cofix !counter, t)
         in
          (match cic_body with
              `AvoidLetInNoAppl n ->
                let n' = List.length inductiveFuns - n in
                 fix_or_cofix n'
            | `AvoidLetIn (n,l) ->
                let n' = List.length inductiveFuns - n in
                 Cic.Appl (fix_or_cofix n'::l)
            | `AddLetIn cic_body ->         
                List.fold_right (build_term inductiveFuns) inductiveFuns
                 cic_body)
    | CicNotationPt.Ident _
    | CicNotationPt.Uri _ when is_path -> raise PathNotWellFormed
    | CicNotationPt.Ident (name, subst)
    | CicNotationPt.Uri (name, subst) as ast ->
        let is_uri = function CicNotationPt.Uri _ -> true | _ -> false in
        (try
          if is_uri ast then raise Not_found;(* don't search the env for URIs *)
          let index = find_in_context name context in
          if subst <> None then
            CicNotationPt.fail loc "Explicit substitutions not allowed here";
          Cic.Rel index
        with Not_found ->
          let cic =
            if is_uri ast then  (* we have the URI, build the term out of it *)
              try
                CicUtil.term_of_uri (UriManager.uri_of_string name)
              with UriManager.IllFormedUri _ ->
                CicNotationPt.fail loc "Ill formed URI"
            else
              resolve env (Id name) ()
          in
          let mk_subst uris =
            let ids_to_uris =
              List.map (fun uri -> UriManager.name_of_uri uri, uri) uris
            in
            (match subst with
            | Some subst ->
                List.map
                  (fun (s, term) ->
                    (try
                      List.assoc s ids_to_uris, aux ~localize loc context term
                     with Not_found ->
                       raise (Invalid_choice (Some loc, lazy "The provided explicit named substitution is trying to instantiate a named variable the object is not abstracted on"))))
                  subst
            | None -> List.map (fun uri -> uri, Cic.Implicit None) uris)
          in
          (try 
            match cic with
            | Cic.Const (uri, []) ->
                let o,_ = CicEnvironment.get_obj CicUniv.empty_ugraph uri in
                let uris = CicUtil.params_of_obj o in
                Cic.Const (uri, mk_subst uris)
            | Cic.Var (uri, []) ->
                let o,_ = CicEnvironment.get_obj CicUniv.empty_ugraph uri in
                let uris = CicUtil.params_of_obj o in
                Cic.Var (uri, mk_subst uris)
            | Cic.MutInd (uri, i, []) ->
               (try
                 let o,_ = CicEnvironment.get_obj CicUniv.empty_ugraph uri in
                 let uris = CicUtil.params_of_obj o in
                 Cic.MutInd (uri, i, mk_subst uris)
                with
                 CicEnvironment.Object_not_found _ ->
                  (* if we are here it is probably the case that during the
                     definition of a mutual inductive type we have met an
                     occurrence of the type in one of its constructors.
                     However, the inductive type is not yet in the environment
                  *)
                  (*here the explicit_named_substituion is assumed to be of length 0 *)
                  Cic.MutInd (uri,i,[]))
            | Cic.MutConstruct (uri, i, j, []) ->
                let o,_ = CicEnvironment.get_obj CicUniv.empty_ugraph uri in
                let uris = CicUtil.params_of_obj o in
                Cic.MutConstruct (uri, i, j, mk_subst uris)
            | Cic.Meta _ | Cic.Implicit _ as t ->
(*
                debug_print (lazy (sprintf
                  "Warning: %s must be instantiated with _[%s] but we do not enforce it"
                  (CicPp.ppterm t)
                  (String.concat "; "
                    (List.map
                      (fun (s, term) -> s ^ " := " ^ CicNotationPtPp.pp_term term)
                      subst))));
*)
                t
            | _ ->
              raise (Invalid_choice (Some loc, lazy "??? Can this happen?"))
           with 
             CicEnvironment.CircularDependency _ -> 
               raise (Invalid_choice (None, lazy "Circular dependency in the environment"))))
    | CicNotationPt.Implicit -> Cic.Implicit None
    | CicNotationPt.UserInput -> Cic.Implicit (Some `Hole)
    | CicNotationPt.Num (num, i) -> resolve env (Num i) ~num ()
    | CicNotationPt.Meta (index, subst) ->
        let cic_subst =
          List.map
            (function
                None -> None
              | Some term -> Some (aux ~localize loc context term))
            subst
        in
        Cic.Meta (index, cic_subst)
    | CicNotationPt.Sort `Prop -> Cic.Sort Cic.Prop
    | CicNotationPt.Sort `Set -> Cic.Sort Cic.Set
    | CicNotationPt.Sort (`Type u) -> Cic.Sort (Cic.Type u)
    | CicNotationPt.Sort `CProp -> Cic.Sort Cic.CProp
    | CicNotationPt.Symbol (symbol, instance) ->
        resolve env (Symbol (symbol, instance)) ()
    | _ -> assert false (* god bless Bologna *)
  and aux_option ~localize loc (context: Cic.name list) annotation = function
    | None -> Cic.Implicit annotation
    | Some term -> aux ~localize loc context term
  in
   aux ~localize:true HExtlib.dummy_floc context ast

let interpretate_path ~context path =
 let localization_tbl = Cic.CicHash.create 23 in
  (* here we are throwing away useful localization informations!!! *)
  fst (
   interpretate_term ~create_dummy_ids:true 
    ~context ~env:Environment.empty ~uri:None ~is_path:true
    path ~localization_tbl, localization_tbl)

let interpretate_obj ~context ~env ~uri ~is_path obj ~localization_tbl =
 assert (context = []);
 assert (is_path = false);
 let interpretate_term = interpretate_term ~localization_tbl in
 match obj with
  | CicNotationPt.Inductive (params,tyl) ->
     let uri = match uri with Some uri -> uri | None -> assert false in
     let context,params =
      let context,res =
       List.fold_left
        (fun (context,res) (name,t) ->
          let t =
           match t with
              None -> CicNotationPt.Implicit
            | Some t -> t in
          let name = CicNotationUtil.cic_name_of_name name in
           name::context,(name, interpretate_term context env None false t)::res
        ) ([],[]) params
      in
       context,List.rev res in
     let add_params =
      List.fold_right (fun (name,ty) t -> Cic.Prod (name,ty,t)) params in
     let name_to_uris =
      snd (
       List.fold_left
        (*here the explicit_named_substituion is assumed to be of length 0 *)
        (fun (i,res) (name,_,_,_) ->
          i + 1,(name,name,Cic.MutInd (uri,i,[]))::res
        ) (0,[]) tyl) in
     let con_env = DisambiguateTypes.env_of_list name_to_uris env in
     let tyl =
      List.map
       (fun (name,b,ty,cl) ->
         let ty' = add_params (interpretate_term context env None false ty) in
         let cl' =
          List.map
           (fun (name,ty) ->
             let ty' =
              add_params (interpretate_term context con_env None false ty)
             in
              name,ty'
           ) cl
         in
          name,b,ty',cl'
       ) tyl
     in
      Cic.InductiveDefinition (tyl,[],List.length params,[])
  | CicNotationPt.Record (params,name,ty,fields) ->
     let uri = match uri with Some uri -> uri | None -> assert false in
     let context,params =
      let context,res =
       List.fold_left
        (fun (context,res) (name,t) ->
          let t =
           match t with
              None -> CicNotationPt.Implicit
            | Some t -> t in
          let name = CicNotationUtil.cic_name_of_name name in
           name::context,(name, interpretate_term context env None false t)::res
        ) ([],[]) params
      in
       context,List.rev res in
     let add_params =
      List.fold_right
       (fun (name,ty) t -> Cic.Prod (name,ty,t)) params in
     let ty' = add_params (interpretate_term context env None false ty) in
     let fields' =
      snd (
       List.fold_left
        (fun (context,res) (name,ty,_coercion,arity) ->
          let context' = Cic.Name name :: context in
           context',(name,interpretate_term context env None false ty)::res
        ) (context,[]) fields) in
     let concl =
      (*here the explicit_named_substituion is assumed to be of length 0 *)
      let mutind = Cic.MutInd (uri,0,[]) in
      if params = [] then mutind
      else
       Cic.Appl
        (mutind::CicUtil.mk_rels (List.length params) (List.length fields)) in
     let con =
      List.fold_left
       (fun t (name,ty) -> Cic.Prod (Cic.Name name,ty,t))
       concl fields' in
     let con' = add_params con in
     let tyl = [name,true,ty',["mk_" ^ name,con']] in
     let field_names = List.map (fun (x,_,y,z) -> x,y,z) fields in
      Cic.InductiveDefinition
       (tyl,[],List.length params,[`Class (`Record field_names)])
  | CicNotationPt.Theorem (flavour, name, ty, bo) ->
     let attrs = [`Flavour flavour] in
     let ty' = interpretate_term [] env None false ty in
     (match bo,flavour with
        None,`Axiom ->
         Cic.Constant (name,None,ty',[],attrs)
      | Some bo,`Axiom -> assert false
      | None,_ ->
         Cic.CurrentProof (name,[],Cic.Implicit None,ty',[],attrs)
      | Some bo,_ ->
         let bo' = Some (interpretate_term [] env None false bo) in
          Cic.Constant (name,bo',ty',[],attrs))
          
let rec domain_of_term ?(loc = HExtlib.dummy_floc) ~context = function
  | Ast.AttributedTerm (`Loc loc, term) ->
     domain_of_term ~loc ~context term
  | Ast.AttributedTerm (_, term) ->
      domain_of_term ~loc ~context term
  | Ast.Symbol (symbol, instance) ->
      [ Node ([loc], Symbol (symbol, instance), []) ]
      (* to be kept in sync with Ast.Appl (Ast.Symbol ...) *)
  | Ast.Appl (Ast.Symbol (symbol, instance) as hd :: args)
  | Ast.Appl (Ast.AttributedTerm (_,Ast.Symbol (symbol, instance)) as hd :: args)
     ->
      let args_dom =
        List.fold_right
          (fun term acc -> domain_of_term ~loc ~context term @ acc)
          args [] in
      let loc =
       match hd with
          Ast.AttributedTerm (`Loc loc,_)  -> loc
        | _ -> loc
      in
       [ Node ([loc], Symbol (symbol, instance), args_dom) ]
  | Ast.Appl (Ast.Ident (name, subst) as hd :: args)
  | Ast.Appl (Ast.AttributedTerm (_,Ast.Ident (name, subst)) as hd :: args) ->
      let args_dom =
        List.fold_right
          (fun term acc -> domain_of_term ~loc ~context term @ acc)
          args [] in
      let loc =
       match hd with
          Ast.AttributedTerm (`Loc loc,_)  -> loc
        | _ -> loc
      in
      (try
        (* the next line can raise Not_found *)
        ignore(find_in_context name context);
        if subst <> None then
          Ast.fail loc "Explicit substitutions not allowed here"
        else
          args_dom
      with Not_found ->
        (match subst with
        | None -> [ Node ([loc], Id name, args_dom) ]
        | Some subst ->
            let terms =
              List.fold_left
                (fun dom (_, term) ->
                  let dom' = domain_of_term ~loc ~context term in
                  dom @ dom')
                [] subst in
            [ Node ([loc], Id name, terms @ args_dom) ]))
  | Ast.Appl terms ->
      List.fold_right
        (fun term acc -> domain_of_term ~loc ~context term @ acc)
        terms []
  | Ast.Binder (kind, (var, typ), body) ->
      let type_dom = domain_of_term_option ~loc ~context typ in
      let body_dom =
        domain_of_term ~loc
          ~context:(CicNotationUtil.cic_name_of_name var :: context) body in
      (match kind with
      | `Exists -> [ Node ([loc], Symbol ("exists", 0), (type_dom @ body_dom)) ]
      | _ -> type_dom @ body_dom)
  | Ast.Case (term, indty_ident, outtype, branches) ->
      let term_dom = domain_of_term ~loc ~context term in
      let outtype_dom = domain_of_term_option ~loc ~context outtype in
      let rec get_first_constructor = function
        | [] -> []
        | (Ast.Pattern (head, _, _), _) :: _ -> [ Node ([loc], Id head, []) ]
        | _ :: tl -> get_first_constructor tl in
      let do_branch =
       function
          Ast.Pattern (head, _, args), term ->
           let (term_context, args_domain) =
             List.fold_left
               (fun (cont, dom) (name, typ) ->
                 (CicNotationUtil.cic_name_of_name name :: cont,
                  (match typ with
                  | None -> dom
                  | Some typ -> dom @ domain_of_term ~loc ~context:cont typ)))
               (context, []) args
           in
            domain_of_term ~loc ~context:term_context term @ args_domain
        | Ast.Wildcard, term ->
            domain_of_term ~loc ~context term
      in
      let branches_dom =
        List.fold_left (fun dom branch -> dom @ do_branch branch) [] branches in
      (match indty_ident with
       | None -> get_first_constructor branches
       | Some (ident, _) -> [ Node ([loc], Id ident, []) ])
      @ term_dom @ outtype_dom @ branches_dom
  | Ast.Cast (term, ty) ->
      let term_dom = domain_of_term ~loc ~context term in
      let ty_dom = domain_of_term ~loc ~context ty in
      term_dom @ ty_dom
  | Ast.LetIn ((var, typ), body, where) ->
      let body_dom = domain_of_term ~loc ~context body in
      let type_dom = domain_of_term_option ~loc ~context typ in
      let where_dom =
        domain_of_term ~loc
          ~context:(CicNotationUtil.cic_name_of_name var :: context) where in
      body_dom @ type_dom @ where_dom
  | Ast.LetRec (kind, defs, where) ->
      let add_defs context =
        List.fold_left
          (fun acc (_, (var, _), _, _) ->
            CicNotationUtil.cic_name_of_name var :: acc
          ) context defs in
      let where_dom = domain_of_term ~loc ~context:(add_defs context) where in
      let defs_dom =
        List.fold_left
          (fun dom (params, (_, typ), body, _) ->
            let context' =
             add_defs
              (List.fold_left
                (fun acc (var,_) -> CicNotationUtil.cic_name_of_name var :: acc)
                context params)
            in
            List.rev
             (snd
               (List.fold_left
                (fun (context,res) (var,ty) ->
                  CicNotationUtil.cic_name_of_name var :: context,
                  domain_of_term_option ~loc ~context ty @ res)
                (add_defs context,[]) params))
            @ domain_of_term_option ~loc ~context:context' typ
            @ domain_of_term ~loc ~context:context' body
          ) [] defs
      in
      defs_dom @ where_dom
  | Ast.Ident (name, subst) ->
      (try
        (* the next line can raise Not_found *)
        ignore(find_in_context name context);
        if subst <> None then
          Ast.fail loc "Explicit substitutions not allowed here"
        else
          []
      with Not_found ->
        (match subst with
        | None -> [ Node ([loc], Id name, []) ]
        | Some subst ->
            let terms =
              List.fold_left
                (fun dom (_, term) ->
                  let dom' = domain_of_term ~loc ~context term in
                  dom @ dom')
                [] subst in
            [ Node ([loc], Id name, terms) ]))
  | Ast.Uri _ -> []
  | Ast.Implicit -> []
  | Ast.Num (num, i) -> [ Node ([loc], Num i, []) ]
  | Ast.Meta (index, local_context) ->
      List.fold_left
       (fun dom term -> dom @ domain_of_term_option ~loc ~context term)
       [] local_context
  | Ast.Sort _ -> []
  | Ast.UserInput
  | Ast.Literal _
  | Ast.Layout _
  | Ast.Magic _
  | Ast.Variable _ -> assert false

and domain_of_term_option ~loc ~context = function
  | None -> []
  | Some t -> domain_of_term ~loc ~context t

let domain_of_term ~context term = 
 uniq_domain (domain_of_term ~context term)

let domain_of_obj ~context ast =
 assert (context = []);
  match ast with
   | Ast.Theorem (_,_,ty,bo) ->
      domain_of_term [] ty
      @ (match bo with
          None -> []
        | Some bo -> domain_of_term [] bo)
   | Ast.Inductive (params,tyl) ->
      let context, dom = 
       List.fold_left
        (fun (context, dom) (var, ty) ->
          let context' = CicNotationUtil.cic_name_of_name var :: context in
          match ty with
             None -> context', dom
           | Some ty -> context', dom @ domain_of_term context ty
        ) ([], []) params in
      let context_w_types =
        List.rev_map
          (fun (var, _, _, _) -> Cic.Name var) tyl
        @ context in
      dom
      @ List.flatten (
         List.map
          (fun (_,_,ty,cl) ->
            domain_of_term context ty
            @ List.flatten (
               List.map
                (fun (_,ty) -> domain_of_term context_w_types ty) cl))
                tyl)
   | CicNotationPt.Record (params,var,ty,fields) ->
      let context, dom = 
       List.fold_left
        (fun (context, dom) (var, ty) ->
          let context' = CicNotationUtil.cic_name_of_name var :: context in
          match ty with
             None -> context', dom
           | Some ty -> context', dom @ domain_of_term context ty
        ) ([], []) params in
      let context_w_types = Cic.Name var :: context in
      dom
      @ domain_of_term context ty
      @ snd
         (List.fold_left
          (fun (context,res) (name,ty,_,_) ->
            Cic.Name name::context, res @ domain_of_term context ty
          ) (context_w_types,[]) fields)

let domain_of_obj ~context obj = 
 uniq_domain (domain_of_obj ~context obj)

  (* dom1 \ dom2 *)
let domain_diff dom1 dom2 =
(* let domain_diff = Domain.diff *)
  let is_in_dom2 elt =
    List.exists
     (function
       | Symbol (symb, 0) ->
          (match elt with
              Symbol (symb',_) when symb = symb' -> true
            | _ -> false)
       | Num i ->
          (match elt with
              Num _ -> true
            | _ -> false)
       | item -> elt = item
     ) dom2
  in
   let rec aux =
    function
       [] -> []
     | Node (_,elt,l)::tl when is_in_dom2 elt -> aux (l @ tl)
     | Node (loc,elt,l)::tl -> Node (loc,elt,aux l)::(aux tl)
   in
    aux dom1

module type Disambiguator =
sig
  val disambiguate_term :
    ?fresh_instances:bool ->
    dbd:HSql.dbd ->
    context:Cic.context ->
    metasenv:Cic.metasenv ->
    ?initial_ugraph:CicUniv.universe_graph -> 
    aliases:DisambiguateTypes.environment ->(* previous interpretation status *)
    universe:DisambiguateTypes.multiple_environment option ->
    CicNotationPt.term disambiguator_input ->
    ((DisambiguateTypes.domain_item * DisambiguateTypes.codomain_item) list *
     Cic.metasenv *                  (* new metasenv *)
     Cic.term*
     CicUniv.universe_graph) list *  (* disambiguated term *)
    bool

  val disambiguate_obj :
    ?fresh_instances:bool ->
    dbd:HSql.dbd ->
    aliases:DisambiguateTypes.environment ->(* previous interpretation status *)
    universe:DisambiguateTypes.multiple_environment option ->
    uri:UriManager.uri option ->     (* required only for inductive types *)
    CicNotationPt.term CicNotationPt.obj disambiguator_input ->
    ((DisambiguateTypes.domain_item * DisambiguateTypes.codomain_item) list *
     Cic.metasenv *                  (* new metasenv *)
     Cic.obj *
     CicUniv.universe_graph) list *  (* disambiguated obj *)
    bool
end

module Make (C: Callbacks) =
  struct
    let choices_of_id dbd id =
      let uris = Whelp.locate ~dbd id in
      let uris =
       match uris with
        | [] ->
           (match 
             (C.input_or_locate_uri 
               ~title:("URI matching \"" ^ id ^ "\" unknown.") ~id ()) 
           with
           | None -> []
           | Some uri -> [uri])
        | [uri] -> [uri]
        | _ ->
            C.interactive_user_uri_choice ~selection_mode:`MULTIPLE
             ~ok:"Try selected." ~enable_button_for_non_vars:true
             ~title:"Ambiguous input." ~id
             ~msg: ("Ambiguous input \"" ^ id ^
                "\". Please, choose one or more interpretations:")
             uris
      in
      List.map
        (fun uri ->
          (UriManager.string_of_uri uri,
           let term =
             try
               CicUtil.term_of_uri uri
             with exn ->
               debug_print (lazy (UriManager.string_of_uri uri));
               debug_print (lazy (Printexc.to_string exn));
               assert false
            in
           fun _ _ _ -> term))
        uris

let refine_profiler = HExtlib.profile "disambiguate_thing.refine_thing"

    let disambiguate_thing ~dbd ~context ~metasenv
      ?(initial_ugraph = CicUniv.empty_ugraph) ~aliases ~universe
      ~uri ~pp_thing ~domain_of_thing ~interpretate_thing ~refine_thing 
      (thing_txt,thing_txt_prefix_len,thing)
    =
      debug_print (lazy "DISAMBIGUATE INPUT");
      let disambiguate_context =  (* cic context -> disambiguate context *)
        List.map
          (function None -> Cic.Anonymous | Some (name, _) -> name)
          context
      in
      debug_print (lazy ("TERM IS: " ^ (pp_thing thing)));
      let thing_dom = domain_of_thing ~context:disambiguate_context thing in
      debug_print
       (lazy (sprintf "DISAMBIGUATION DOMAIN: %s"(string_of_domain thing_dom)));
(*
      debug_print (lazy (sprintf "DISAMBIGUATION ENVIRONMENT: %s"
        (DisambiguatePp.pp_environment aliases)));
      debug_print (lazy (sprintf "DISAMBIGUATION UNIVERSE: %s"
        (match universe with None -> "None" | Some _ -> "Some _")));
*)
      let current_dom =
        Environment.fold (fun item _ dom -> item :: dom) aliases [] in
      let todo_dom = domain_diff thing_dom current_dom in
      debug_print
       (lazy (sprintf "DISAMBIGUATION DOMAIN AFTER DIFF: %s"(string_of_domain todo_dom)));
      (* (2) lookup function for any item (Id/Symbol/Num) *)
      let lookup_choices =
        fun item ->
          let choices =
            let lookup_in_library () =
              match item with
              | Id id -> choices_of_id dbd id
              | Symbol (symb, _) ->
                 (try
                   List.map DisambiguateChoices.mk_choice
                    (TermAcicContent.lookup_interpretations symb)
                  with
                   TermAcicContent.Interpretation_not_found -> [])
              | Num instance ->
                  DisambiguateChoices.lookup_num_choices ()
            in
            match universe with
            | None -> lookup_in_library ()
            | Some e ->
                (try
                  let item =
                    match item with
                    | Symbol (symb, _) -> Symbol (symb, 0)
                    | item -> item
                  in
                  Environment.find item e
                with Not_found -> lookup_in_library ())
          in
          choices
      in
(*
      (* <benchmark> *)
      let _ =
        if benchmark then begin
          let per_item_choices =
            List.map
              (fun dom_item ->
                try
                  let len = List.length (lookup_choices dom_item) in
                  debug_print (lazy (sprintf "BENCHMARK %s: %d"
                    (string_of_domain_item dom_item) len));
                  len
                with No_choices _ -> 0)
              thing_dom
          in
          max_refinements := List.fold_left ( * ) 1 per_item_choices;
          actual_refinements := 0;
          domain_size := List.length thing_dom;
          choices_avg :=
            (float_of_int !max_refinements) ** (1. /. float_of_int !domain_size)
        end
      in
      (* </benchmark> *)
*)

      (* (3) test an interpretation filling with meta uninterpreted identifiers
       *)
      let test_env aliases todo_dom ugraph = 
        let rec aux env = function
          | [] -> env
          | Node (_, item, l) :: tl ->
              let env =
                Environment.add item
                 ("Implicit",
                   (match item with
                      | Id _ | Num _ ->
                          (fun _ _ _ -> Cic.Implicit (Some `Closed))
                      | Symbol _ -> (fun _ _ _ -> Cic.Implicit None)))
                 env in
              aux (aux env l) tl in
        let filled_env = aux aliases todo_dom in
        try
          let localization_tbl = Cic.CicHash.create 503 in
          let cic_thing =
            interpretate_thing ~context:disambiguate_context ~env:filled_env
             ~uri ~is_path:false thing ~localization_tbl
          in
let foo () =
          let k,ugraph1 =
           refine_thing metasenv context uri cic_thing ugraph ~localization_tbl
          in
            (k , ugraph1 )
in refine_profiler.HExtlib.profile foo ()
        with
        | Try_again msg -> Uncertain (None,msg), ugraph
        | Invalid_choice (loc,msg) -> Ko (loc,msg), ugraph
      in
      (* (4) build all possible interpretations *)
      let (@@) (l1,l2,l3) (l1',l2',l3') = l1@l1', l2@l2', l3@l3' in
      (* aux returns triples Ok/Uncertain/Ko *)
      (* rem_dom is the concatenation of all the remaining domains *)
      let rec aux aliases diff lookup_in_todo_dom todo_dom rem_dom base_univ =
        (* debug_print (lazy ("ZZZ: " ^ string_of_domain todo_dom)); *)
        match todo_dom with
        | Node (locs,item,inner_dom) ->
            debug_print (lazy (sprintf "CHOOSED ITEM: %s"
             (string_of_domain_item item)));
            let choices =
             match lookup_in_todo_dom with
                None -> lookup_choices item
              | Some choices -> choices in
            match choices with
               [] ->
                [], [],
                 [aliases, diff, Some (List.hd locs),
                  lazy ("No choices for " ^ string_of_domain_item item),
                  true]
(*
             | [codomain_item] ->
                 (* just one choice. We perform a one-step look-up and
                    if the next set of choices is also a singleton we
                    skip this refinement step *)
                 debug_print(lazy (sprintf "%s CHOSEN" (fst codomain_item)));
                 let new_env = Environment.add item codomain_item aliases in
                 let new_diff = (item,codomain_item)::diff in
                 let lookup_in_todo_dom,next_choice_is_single =
                  match remaining_dom with
                     [] -> None,false
                   | (_,he)::_ ->
                      let choices = lookup_choices he in
                       Some choices,List.length choices = 1
                 in
                  if next_choice_is_single then
                   aux new_env new_diff lookup_in_todo_dom remaining_dom
                    base_univ
                  else
                    (match test_env new_env remaining_dom base_univ with
                    | Ok (thing, metasenv),new_univ ->
                        (match remaining_dom with
                        | [] ->
                           [ new_env, new_diff, metasenv, thing, new_univ ], []
                        | _ ->
                           aux new_env new_diff lookup_in_todo_dom
                            remaining_dom new_univ)
                    | Uncertain (loc,msg),new_univ ->
                        (match remaining_dom with
                        | [] -> [], [new_env,new_diff,loc,msg,true]
                        | _ ->
                           aux new_env new_diff lookup_in_todo_dom
                            remaining_dom new_univ)
                    | Ko (loc,msg),_ -> [], [new_env,new_diff,loc,msg,true])
*)
             | _::_ ->
               let outcomes =
                List.map
                 (function codomain_item ->
                   debug_print(lazy (sprintf "%s CHOSEN" (fst codomain_item)));
                   let new_env = Environment.add item codomain_item aliases in
                   let new_diff = (item,codomain_item)::diff in
                     test_env new_env (inner_dom@rem_dom) base_univ,
                      new_env,new_diff
                 ) choices in
               let some_outcome_ok =
                List.exists
                 (function
                     (Ok (_,_),_),_,_
                   | (Uncertain (_,_),_),_,_ -> true
                   | _ -> false)
                 outcomes in
               let rec filter univ = function 
                | [] -> [],[],[]
                | (outcome,new_env,new_diff) :: tl ->
                   match outcome with
                    | Ok (thing, metasenv),new_univ ->
                        let res = 
                          (match inner_dom with
                          | [] ->
                             [new_env,new_diff,metasenv,thing,new_univ], [], []
                          | _ ->
                             visit_children new_env new_diff new_univ rem_dom inner_dom)
                        in
                         res @@ filter univ tl
                    | Uncertain (loc,msg),new_univ ->
                        let res = 
                          (match inner_dom with
                          | [] -> [],[new_env,new_diff,loc,msg,new_univ],[]
                          | _ ->
                             visit_children new_env new_diff new_univ rem_dom inner_dom)
                        in
                         res @@ filter univ tl
                    | Ko (loc,msg),_ ->
                        let res =
                         [],[],[new_env,new_diff,loc,msg,not some_outcome_ok]
                        in
                         res @@ filter univ tl
               in
                filter base_univ outcomes
      and visit_children env diff univ rem_dom =
       function
          [] -> assert false
        | [dom] -> aux env diff None dom rem_dom univ
        | dom::remaining_dom ->
           let ok_l,uncertain_l,error_l =
            aux env diff None dom (remaining_dom@rem_dom) univ
           in
            let res_after_ok_l =
             List.fold_right
              (fun (env,diff,_,_,univ) res ->
                visit_children env diff univ rem_dom remaining_dom
                @@ res
              ) ok_l ([],[],error_l)
            in
             List.fold_right
              (fun (env,diff,_,_,univ) res ->
                visit_children env diff univ rem_dom remaining_dom
                @@ res
              ) uncertain_l res_after_ok_l
      in
      let aux' aliases diff lookup_in_todo_dom todo_dom base_univ =
       match test_env aliases todo_dom base_univ with
        | Ok (thing, metasenv),new_univ -> 
           if todo_dom = [] then
            [ aliases, diff, metasenv, thing, new_univ ], [], []
           else
            visit_children aliases diff base_univ [] todo_dom
(*
              _lookup_in_todo_dom_
*)
        | Uncertain (loc,msg),new_univ ->
           if todo_dom = [] then
            [],[aliases,diff,loc,msg,new_univ],[]
           else
            visit_children aliases diff base_univ [] todo_dom
(*
              _lookup_in_todo_dom_
*)
        | Ko (loc,msg),_ -> [],[],[aliases,diff,loc,msg,true] in
      let base_univ = initial_ugraph in
      try
        let res =
         match aux' aliases [] None todo_dom base_univ with
         | [],uncertain,errors ->
            debug_print (lazy "NO INTERPRETATIONS");
            let errors =
             List.map
              (fun (env,diff,loc,msg,_) -> (env,diff,loc,msg,true)
              ) uncertain @ errors
            in
            let errors =
             List.map
              (fun (env,diff,loc,msg,significant) ->
                let env' =
                 filter_map_domain
                   (fun locs domain_item ->
                     try
                      let description =
                       fst (Environment.find domain_item env)
                      in
                       Some (locs,descr_of_domain_item domain_item,description)
                     with
                      Not_found -> None)
                   thing_dom
                in
                 env',diff,loc,msg,significant
              ) errors
            in
             raise (NoWellTypedInterpretation (0,errors))
         | [_,diff,metasenv,t,ugraph],_,_ ->
             debug_print (lazy "SINGLE INTERPRETATION");
             [diff,metasenv,t,ugraph], false
         | l,_,_ ->
             debug_print 
               (lazy (sprintf "MANY INTERPRETATIONS (%d)" (List.length l)));
             let choices =
               List.map
                 (fun (env, _, _, _, _) ->
                   map_domain
                     (fun locs domain_item ->
                       let description =
                         fst (Environment.find domain_item env)
                       in
                       locs,descr_of_domain_item domain_item, description)
                     thing_dom)
                 l
             in
             let choosed = 
               C.interactive_interpretation_choice 
                 thing_txt thing_txt_prefix_len choices 
             in
             (List.map (fun n->let _,d,m,t,u= List.nth l n in d,m,t,u) choosed),
              true
        in
         res
     with
      CicEnvironment.CircularDependency s -> 
        failwith "Disambiguate: circular dependency"

    let disambiguate_term ?(fresh_instances=false) ~dbd ~context ~metasenv
      ?(initial_ugraph = CicUniv.empty_ugraph) ~aliases ~universe 
      (text,prefix_len,term)
    =
      let term =
        if fresh_instances then CicNotationUtil.freshen_term term else term
      in
      disambiguate_thing ~dbd ~context ~metasenv ~initial_ugraph ~aliases
        ~universe ~uri:None ~pp_thing:CicNotationPp.pp_term
        ~domain_of_thing:domain_of_term
        ~interpretate_thing:(interpretate_term (?create_dummy_ids:None))
        ~refine_thing:refine_term (text,prefix_len,term)

    let disambiguate_obj ?(fresh_instances=false) ~dbd ~aliases ~universe ~uri
     (text,prefix_len,obj)
    =
      let obj =
        if fresh_instances then CicNotationUtil.freshen_obj obj else obj
      in
      disambiguate_thing ~dbd ~context:[] ~metasenv:[] ~aliases ~universe ~uri
        ~pp_thing:(CicNotationPp.pp_obj CicNotationPp.pp_term) ~domain_of_thing:domain_of_obj
        ~interpretate_thing:interpretate_obj ~refine_thing:refine_obj
        (text,prefix_len,obj)
  end

