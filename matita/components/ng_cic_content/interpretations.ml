(* Copyright (C) 2005, HELM Team.
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

(* $Id: interpretations.ml 13145 2016-03-13 17:30:14Z fguidi $ *)

open Printf

module Ast = NotationPt


let debug = false
let debug_print s = if debug then prerr_endline (Lazy.force s) else ()

type id = string
let hide_coercions = ref true;;

type cic_id = string

type term_info =
  { sort: (cic_id, Ast.sort_kind) Hashtbl.t;
    uri: (cic_id, NReference.reference) Hashtbl.t;
  }

module IntMap = Map.Make(struct type t = int let compare = compare end);;
module StringMap = Map.Make(String);;

type db = {
  counter: int;
  pattern32_matrix: (bool * NotationPt.cic_appl_pattern * int) list;
  level2_patterns32:
   (string * string * NotationPt.argument_pattern list *
     NotationPt.cic_appl_pattern) IntMap.t;
  interpretations: int list StringMap.t; (* symb -> id list *)
  compiled32:
   (NCic.term -> ((string * NCic.term) list * NCic.term list * int) option)
    Lazy.t
}

let initial_db status = {
   counter = -1; 
   pattern32_matrix = [];
   level2_patterns32 = IntMap.empty;
   interpretations = StringMap.empty;
   compiled32 = lazy (Ncic2astMatcher.Matcher32.compiler status [])
}

class type g_status =
  object
    inherit NCicCoercion.g_status
    method interp_db: db
  end
 
class virtual status =
 object(self)
   inherit NCicCoercion.status
   val mutable interp_db = None (* mutable only to initialize it :-( *)
   method interp_db = match interp_db with None -> assert false | Some x -> x
   method set_interp_db v = {< interp_db = Some v >}
   method set_interp_status
    : 'status. #g_status as 'status -> 'self
    = fun o -> {< interp_db = Some o#interp_db >}#set_coercion_status o
   initializer
    interp_db <- Some (initial_db self)
 end

let idref register_ref =
 let id = ref 0 in
  fun ?reference t ->
   incr id;
   let id = "i" ^ string_of_int !id in
    (match reference with None -> () | Some r -> register_ref id r);
    Ast.AttributedTerm (`IdRef id, t)
;;

let level_of_uri u = 
  let name = NUri.name_of_uri u in
  assert(String.length name > String.length "Type");
  String.sub name 4 (String.length name - 4)
;;

let find_level2_patterns32 status pid =
 IntMap.find pid status#interp_db.level2_patterns32

let add_idrefs =
  List.fold_right (fun idref t -> Ast.AttributedTerm (`IdRef idref, t))

let instantiate32 idrefs env symbol args =
  let rec instantiate_arg = function
    | Ast.IdentArg (n, name) ->
        let t = 
          try List.assoc name env 
          with Not_found -> prerr_endline ("name not found in env: "^name);
                            assert false
        in
        let rec count_lambda = function
          | Ast.AttributedTerm (_, t) -> count_lambda t
          | Ast.Binder (`Lambda, _, body) -> 1 + count_lambda body
          | _ -> 0
        in
        let rec add_lambda t n =
          if n > 0 then
            let name = NotationUtil.fresh_name () in
            Ast.Binder (`Lambda, (Ast.Ident (name, None), None),
              Ast.Appl [add_lambda t (n - 1); Ast.Ident (name, None)])
          else
            t
        in
        add_lambda t (n - count_lambda t)
  in
  let head =
    let symbol = Ast.Symbol (symbol, 0) in
    add_idrefs idrefs symbol
  in
  if args = [] then head
  else Ast.Appl (head :: List.map instantiate_arg args)

let fresh_id status =
  let counter = status#interp_db.counter+1 in
   status#set_interp_db ({ status#interp_db with counter = counter  }), counter

let load_patterns32 status t =
 let t =
  HExtlib.filter_map (function (true, ap, id) -> Some (ap, id) | _ -> None) t
 in
  status#set_interp_db
   {status#interp_db with
     compiled32 = lazy (Ncic2astMatcher.Matcher32.compiler status t) }
;;

let add_interpretation status dsc (symbol, args) appl_pattern =
  let status,id = fresh_id status in
  let ids =
   try
    id::StringMap.find symbol status#interp_db.interpretations
   with Not_found -> [id] in
  let status =
   status#set_interp_db { status#interp_db with
    level2_patterns32 =
      IntMap.add id (dsc, symbol, args, appl_pattern)
       status#interp_db.level2_patterns32;
    pattern32_matrix = (true,appl_pattern,id)::status#interp_db.pattern32_matrix;
    interpretations = StringMap.add symbol ids status#interp_db.interpretations
   }
  in
   load_patterns32 status status#interp_db.pattern32_matrix

let toggle_active_interpretations status b =
  status#set_interp_db { status#interp_db with
   pattern32_matrix =
     List.map (fun (_,ap,id) -> b,ap,id) status#interp_db.pattern32_matrix }

exception Interpretation_not_found

let lookup_interpretations status ?(sorted=true) symbol =
  try
    let raw = 
      List.map (
        fun id ->
          let (dsc, _, args, appl_pattern) =
            try IntMap.find id status#interp_db.level2_patterns32
            with Not_found -> assert false 
          in
          dsc, args, appl_pattern
      ) (StringMap.find symbol status#interp_db.interpretations)
    in
    if sorted then HExtlib.list_uniq (List.sort Pervasives.compare raw)
              else raw
  with Not_found -> raise Interpretation_not_found

let instantiate_appl_pattern 
  ~mk_appl ~mk_implicit ~term_of_nref env appl_pattern 
=
  let lookup name =
    try List.assoc name env
    with Not_found ->
      prerr_endline (sprintf "Name %s not found" name);
      assert false
  in
  let rec aux = function
    | Ast.NRefPattern nref -> term_of_nref nref
    | Ast.ImplicitPattern -> mk_implicit false
    | Ast.VarPattern name -> lookup name
    | Ast.ApplPattern terms -> mk_appl (List.map aux terms)
  in
  aux appl_pattern

let destroy_nat =
  let is_nat_URI = NUri.eq (NUri.uri_of_string
  "cic:/matita/arithmetics/nat/nat.ind") in
  let is_zero = function
    | NCic.Const (NReference.Ref (uri, NReference.Con (0, 1, 0))) when
       is_nat_URI uri -> true
    | _ -> false
  in
  let is_succ = function
    | NCic.Const (NReference.Ref (uri, NReference.Con (0, 2, 0))) when
       is_nat_URI uri -> true
    | _ -> false
  in
  let rec aux acc = function
    | NCic.Appl [he ; tl] when is_succ he -> aux (acc + 1) tl
    | t when is_zero t -> Some acc
    | _ -> None
  in
   aux 0

(* CODICE c&p da NCicPp *)
let nast_of_cic0 status
 ~(idref:
    ?reference:NReference.reference -> NotationPt.term -> NotationPt.term)
 ~output_type ~metasenv ~subst k ~context =
  function
    | NCic.Rel n ->
       (try 
         let name,_ = List.nth context (n-1) in
         let name = if name = "_" then "__"^string_of_int n else name in
          idref (Ast.Ident (name,None))
        with Failure "nth" | Invalid_argument "List.nth" -> 
         idref (Ast.Ident ("-" ^ string_of_int (n - List.length context),None)))
    | NCic.Const r -> idref ~reference:r (Ast.Ident (NCicPp.r2s status true r, None))
    | NCic.Meta (n,lc) when List.mem_assoc n subst -> 
        let _,_,t,_ = List.assoc n subst in
         k ~context (NCicSubstitution.subst_meta status lc t)
    | NCic.Meta (n,(s,l)) ->
       (* CSC: qua non dovremmo espandere *)
       let l = NCicUtils.expand_local_context l in
        idref (Ast.Meta
         (n, List.map (fun x -> Some (k ~context (NCicSubstitution.lift status s x))) l))
    | NCic.Sort NCic.Prop -> idref (Ast.Sort `Prop)
    | NCic.Sort NCic.Type [] -> idref (Ast.Sort `Set)
    | NCic.Sort NCic.Type ((`Type,u)::_) -> 
              idref(Ast.Sort (`NType (level_of_uri u)))
    | NCic.Sort NCic.Type ((`CProp,u)::_) -> 
              idref(Ast.Sort (`NCProp (level_of_uri u)))
    | NCic.Sort NCic.Type ((`Succ,u)::_) -> 
              idref(Ast.Sort (`NType (level_of_uri u ^ "+1")))
    | NCic.Implicit `Hole -> idref (Ast.UserInput)
    | NCic.Implicit `Vector -> idref (Ast.Implicit `Vector)
    | NCic.Implicit _ -> idref (Ast.Implicit `JustOne)
    | NCic.Prod (n,s,t) ->
        let n = if n.[0] = '_' then "_" else n in
        let binder_kind = `Forall in
         idref (Ast.Binder (binder_kind, (Ast.Ident (n,None), Some (k ~context s)),
          k ~context:((n,NCic.Decl s)::context) t))
    | NCic.Lambda (n,s,t) ->
        idref (Ast.Binder (`Lambda,(Ast.Ident (n,None), Some (k ~context s)),
         k ~context:((n,NCic.Decl s)::context) t))
    | NCic.LetIn (n,s,ty,NCic.Rel 1) ->
        idref (Ast.Cast (k ~context ty, k ~context s))
    | NCic.LetIn (n,s,ty,t) ->
        idref (Ast.LetIn ((Ast.Ident (n,None), Some (k ~context s)), k ~context
          ty, k ~context:((n,NCic.Decl s)::context) t))
    | NCic.Appl (NCic.Meta (n,lc) :: args) when List.mem_assoc n subst -> 
       let _,_,t,_ = List.assoc n subst in
       let hd = NCicSubstitution.subst_meta status lc t in
        k ~context
         (NCicReduction.head_beta_reduce status ~upto:(List.length args)
           (match hd with
           | NCic.Appl l -> NCic.Appl (l@args)
           | _ -> NCic.Appl (hd :: args)))
    | NCic.Appl args as t ->
       (match destroy_nat t with
         | Some n -> idref (Ast.Num (string_of_int n, -1))
         | None ->
            let args =
             if not !hide_coercions then args
             else
              match
               NCicCoercion.match_coercion status ~metasenv ~context ~subst t
              with
               | None -> args
               | Some (_,sats,cpos) -> 
(* CSC: sats e' il numero di pi, ma non so cosa farmene! voglio il numero di
   argomenti da saltare, come prima! *)
                  if cpos < List.length args - 1 then
                   List.nth args (cpos + 1) ::
                    try snd (HExtlib.split_nth (cpos+sats+2) args)
                    with Failure _->[]
                  else
                   args
            in
             (match args with
                 [arg] -> idref (k ~context arg)
               | _ -> idref (Ast.Appl (List.map (k ~context) args))))
    | NCic.Match (NReference.Ref (uri,_) as r,outty,te,patterns) ->
       (try
        let name = NUri.name_of_uri uri in
(* CSC
        let uri_str = UriManager.string_of_uri uri in
        let puri_str = sprintf "%s#xpointer(1/%d)" uri_str (typeno+1) in
        let ctor_puri j =
          UriManager.uri_of_string
            (sprintf "%s#xpointer(1/%d/%d)" uri_str (typeno+1) j)
        in
*)
        let case_indty =
         name, None(*CSC Some (UriManager.uri_of_string puri_str)*) in
        let constructors, leftno =
         let _,leftno,tys,_,n = NCicEnvironment.get_checked_indtys status r in
         let _,_,_,cl  = List.nth tys n in
          cl,leftno
        in
	let rec eat_branch n ctx ty pat =
          match (ty, pat) with
	  | NCic.Prod (name, s, t), _ when n > 0 ->
             eat_branch (pred n) ctx t pat 
          | NCic.Prod (_, _, t), NCic.Lambda (name, s, t') ->
              let cv, rhs = eat_branch 0 ((name,NCic.Decl s)::ctx) t t' in
              (Ast.Ident (name,None), Some (k ~context:ctx s)) :: cv, rhs
          | _, _ -> [], k ~context:ctx pat
        in
        let j = ref 0 in
        let patterns =
          try
            List.map2
              (fun (_, name, ty) pat ->
                incr j;
                let name,(capture_variables,rhs) =
                 match output_type with
                    `Term -> name, eat_branch leftno context ty pat
                  | `Pattern -> "_", ([], k ~context pat)
                in
                 Ast.Pattern (name, None(*CSC Some (ctor_puri !j)*), capture_variables), rhs
              ) constructors patterns
          with Invalid_argument _ -> assert false
        in
        let indty =
         match output_type with
            `Pattern -> None
          | `Term -> Some case_indty
        in
         idref (Ast.Case (k ~context te, indty, Some (k ~context outty), patterns))
     with
      NCicEnvironment.ObjectNotFound msg ->
       idref (Ast.Case(k ~context te,Some ("NOT_FOUND: " ^ Lazy.force msg,None),
       Some (k ~context outty),
       (List.map (fun t -> Ast.Pattern ("????", None, []), k ~context t)
         patterns))))
;;

let rec nast_of_cic1 status ~idref ~output_type ~metasenv ~subst ~context term =
  match Lazy.force status#interp_db.compiled32 term with
  | None ->
     nast_of_cic0 status ~idref ~output_type ~metasenv ~subst
      (nast_of_cic1 status ~idref ~output_type ~metasenv ~subst) ~context term 
  | Some (env, ctors, pid) -> 
      let idrefs =
       List.map
        (fun term ->
          let attrterm =
           idref
            ~reference:
              (match term with NCic.Const nref -> nref | _ -> assert false)
           (NotationPt.Ident ("dummy",None))
          in
           match attrterm with
              Ast.AttributedTerm (`IdRef id, _) -> id
            | _ -> assert false
        ) ctors
      in
      let env =
       List.map
        (fun (name, term) ->
          name,
           nast_of_cic1 status ~idref ~output_type ~subst ~metasenv ~context
            term
        ) env
      in
      let _, symbol, args, _ =
        try
         find_level2_patterns32 status pid
        with Not_found -> assert false
      in
      let ast = instantiate32 idrefs env symbol args in
      idref ast (*Ast.AttributedTerm (`IdRef (idref term), ast)*)
;;

let nmap_context0 status ~idref ~metasenv ~subst context =
 let module K = Content in
 let nast_of_cic =
  nast_of_cic1 status ~idref ~output_type:`Term ~metasenv ~subst
 in
 fst (
  List.fold_right
   (fun item (res,context) ->
     match item with
      | name,NCic.Decl t ->
         Some
          (* We should call build_decl_item, but we have not computed *)
          (* the inner-types ==> we always produce a declaration      *)
          (`Declaration
            { K.dec_name = (Some name);
              K.dec_id = "-1"; 
              K.dec_inductive = false;
              K.dec_aref = "-1";
              K.dec_type = nast_of_cic ~context t
            })::res,item::context
      | name,NCic.Def (t,ty) ->
         Some
          (* We should call build_def_item, but we have not computed *)
          (* the inner-types ==> we always produce a declaration     *)
          (`Definition
             { K.def_name = (Some name);
               K.def_id = "-1"; 
               K.def_aref = "-1";
               K.def_term = nast_of_cic ~context t;
               K.def_type = nast_of_cic ~context ty
             })::res,item::context
   ) context ([],[]))
;;

let nmap_sequent0 status ~idref ~metasenv ~subst (i,(n,context,ty)) =
 let module K = Content in
 let nast_of_cic =
  nast_of_cic1 status ~idref ~output_type:`Term ~metasenv ~subst in
 let context' = nmap_context0 status ~idref ~metasenv ~subst context in
  ("-1",i,context',nast_of_cic ~context ty)
;;

let object_prefix = "obj:";;
let declaration_prefix = "decl:";;
let definition_prefix = "def:";;
let inductive_prefix = "ind:";;
let joint_prefix = "joint:";;

let get_id =
 function
    Ast.AttributedTerm (`IdRef id, _) -> id
  | _ -> assert false
;;

let gen_id prefix seed =
 let res = prefix ^ string_of_int !seed in
  incr seed ;
  res
;;

let build_def_item seed context metasenv id n t ty =
 let module K = Content in
(*
  try
   let sort = Hashtbl.find ids_to_inner_sorts id in
   if sort = `Prop then
       (let p = 
        (acic2content seed context metasenv ?name:(name_of n) ~ids_to_inner_sorts  ~ids_to_inner_types t)
       in 
        `Proof p;)
   else 
*)
      `Definition
        { K.def_name = Some n;
          K.def_id = gen_id definition_prefix seed; 
          K.def_aref = id;
          K.def_term = t;
          K.def_type = ty
        }
(*
  with
   Not_found -> assert false
*)

let build_decl_item seed id n s =
 let module K = Content in
(*
 let sort =
   try
    Some (Hashtbl.find ids_to_inner_sorts (Cic2acic.source_id_of_id id))
   with Not_found -> None
 in
 match sort with
 | Some `Prop ->
    `Hypothesis
      { K.dec_name = name_of n;
        K.dec_id = gen_id declaration_prefix seed; 
        K.dec_inductive = false;
        K.dec_aref = id;
        K.dec_type = s
      }
 | _ ->
*)
    `Declaration
      { K.dec_name = Some n;
        K.dec_id = gen_id declaration_prefix seed; 
        K.dec_inductive = false;
        K.dec_aref = id;
        K.dec_type = s
      }
;;

let nmap_cobj0 status ~idref (uri,_,metasenv,subst,kind) =
  let module K = Content in
  let nast_of_cic =
   nast_of_cic1 status ~idref ~output_type:`Term ~metasenv ~subst in
  let seed = ref 0 in
  let conjectures =
   match metasenv with
      [] -> None
    | _ -> (*Some (List.map (map_conjectures seed) metasenv)*)
      (*CSC: used to be the previous line, that uses seed *)
      Some (List.map (nmap_sequent0 status ~idref ~metasenv ~subst) metasenv)
  in
let  build_constructors seed l =
      List.map 
       (fun (_,n,ty) ->
           let ty = nast_of_cic ~context:[] ty in
           { K.dec_name = Some n;
             K.dec_id = gen_id declaration_prefix seed;
             K.dec_inductive = false;
             K.dec_aref = "";
             K.dec_type = ty
           }) l
in
let build_inductive b seed = 
      fun (_,n,ty,cl) ->
        let ty = nast_of_cic ~context:[] ty in
        `Inductive
          { K.inductive_id = gen_id inductive_prefix seed;
            K.inductive_name = n;
            K.inductive_kind = b;
            K.inductive_type = ty;
            K.inductive_constructors = build_constructors seed cl
           }
in
let build_fixpoint b seed = 
      fun (_,n,_,ty,t) ->
        let t = nast_of_cic ~context:[] t in
        let ty = nast_of_cic ~context:[] ty in
        `Definition
          { K.def_id = gen_id inductive_prefix seed;
            K.def_name = Some n;
            K.def_aref = "";
            K.def_type = ty;
            K.def_term = t;
           }
in
 match kind with
  | NCic.Fixpoint (is_rec, ifl, _) -> 
       (gen_id object_prefix seed, conjectures,
          `Joint
            { K.joint_id = gen_id joint_prefix seed;
              K.joint_kind = 
                 if is_rec then 
                      `Recursive (List.map (fun (_,_,i,_,_) -> i) ifl)
                 else `CoRecursive;
              K.joint_defs = List.map (build_fixpoint is_rec seed) ifl
            }) 
  | NCic.Inductive (is_ind, lno, itl, _) ->
       (gen_id object_prefix seed, conjectures,
          `Joint
            { K.joint_id = gen_id joint_prefix seed;
              K.joint_kind = 
                 if is_ind then `Inductive lno else `CoInductive lno;
              K.joint_defs = List.map (build_inductive is_ind seed) itl
            }) 
  | NCic.Constant (_,_,Some bo,ty,_) ->
     let ty = nast_of_cic ~context:[] ty in
     let bo = nast_of_cic ~context:[] bo in
      (gen_id object_prefix seed, conjectures,
        `Def (K.Const,ty,
          build_def_item seed [] [] (get_id bo) (NUri.name_of_uri uri) bo ty))
  | NCic.Constant (_,_,None,ty,_) ->
     let ty = nast_of_cic ~context:[] ty in
       (gen_id object_prefix seed, conjectures,
         `Decl (K.Const,
           (*CSC: ??? get_id ty here used to be the id of the axiom! *)
           build_decl_item seed (get_id ty) (NUri.name_of_uri uri) ty))
;;

let with_idrefs foo status obj =
 let ids_to_refs = Hashtbl.create 211 in
 let register_ref = Hashtbl.add ids_to_refs in
  foo status ~idref:(idref register_ref) obj, ids_to_refs
;;

let nmap_cobj status = with_idrefs nmap_cobj0 status

let nmap_sequent status ~metasenv ~subst =
 with_idrefs (nmap_sequent0 ~metasenv ~subst) status

let nmap_term status ~metasenv ~subst ~context =
 with_idrefs (nast_of_cic1 ~output_type:`Term ~metasenv ~subst ~context) status

let nmap_context status ~metasenv ~subst =
 with_idrefs (nmap_context0 ~metasenv ~subst) status

(* FG ***********************************************************************)

let nmap_obj0 status ~idref (_, _, metasenv, subst, kind) =
   let module N = NotationPt in
   let nast_of_cic =
      nast_of_cic1 status ~idref ~output_type:`Term ~metasenv ~subst
   in
   let rec mk_captures lno k c u = match lno, u with
      | 0, _                                -> k, c
      | _, NCic.Prod (n, w, u) when lno > 0 ->
         let cap = nast_of_cic ~context:c w, None in
	 let hyp = n, NCic.Decl w in
	 mk_captures (pred lno) (cap :: k) (hyp :: c) u
      | _                                 -> assert false
   in
   let build_captures lno = function
      | []                -> [], []
      | (_, _, u, _) :: _ -> mk_captures lno [] [] u
   in
   let rec eat_prods prods lno t = match prods, lno, t with
      | _, 0, _                                      -> t
      | true, _, NCic.Prod (_, _, t) when lno > 0    -> eat_prods prods (pred lno) t
      | false, _, NCic.Lambda (_, _, t) when lno > 0 -> eat_prods prods (pred lno) t
      | _                                            -> assert false
   in
   let build_constractor lno context (_, n, bo) =
      let bo = nast_of_cic ~context (eat_prods false lno bo) in      
      n, bo
   in
   let build_inductive is_ind lno context (_, n, ty, cl) =
      let ty = nast_of_cic ~context (eat_prods true lno ty) in
      n, is_ind, ty, List.map (build_constractor lno context) cl
   in
   match kind with
      | NCic.Constant (_, n, xbo, ty, attrs) ->
	 let ty = nast_of_cic ~context:[] ty in
         let xbo = match xbo with 
	    | Some bo -> Some (nast_of_cic ~context:[] bo)
	    | None    -> None
	 in
	 N.Theorem (n, ty, xbo, attrs)
      | NCic.Inductive (is_ind, lno, itl, (src, `Regular)) ->      
         let captures, context = build_captures lno itl in
	 N.Inductive (captures, List.map (build_inductive is_ind lno context) itl, src)
      | _ -> assert false  (* NCic.Fixpoint (is_rec, ifl, _) -> *)

let nmap_obj status = with_idrefs nmap_obj0 status
