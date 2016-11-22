(* Copyright (C) 2000, HELM Team.
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

(* $Id: cicPp.ml 7413 2007-05-29 15:30:53Z tassi $ *)

module Ref = NReference

let fix_sorts t = t;;
let apply_subst subst t = assert (subst=[]); t;;

type typformerreference = Ref.reference
type reference = Ref.reference

type kind =
  | Type
  | KArrow of kind * kind
  | KSkip of kind (* dropped abstraction *)

let rec size_of_kind =
  function
    | Type -> 1
    | KArrow (l, r) -> 1 + size_of_kind l + size_of_kind r
    | KSkip k -> size_of_kind k
;;

let bracket ?(prec=1) size_of pp o =
  if size_of o > prec then
    "(" ^ pp o ^ ")"
  else
    pp o
;;

let rec pretty_print_kind =
  function
    | Type -> "*"
    | KArrow (l, r) -> bracket size_of_kind pretty_print_kind l ^ " -> " ^ pretty_print_kind r
    | KSkip k -> pretty_print_kind k
;;

type typ =
  | Var of int
  | Unit
  | Top
  | TConst of typformerreference
  | Arrow of typ * typ
  | TSkip of typ
  | Forall of string * kind * typ
  | TAppl of typ list

let rec size_of_type =
  function
    | Var _ -> 0
    | Unit -> 0
    | Top -> 0
    | TConst _ -> 0
    | Arrow _ -> 2
    | TSkip t -> size_of_type t
    | Forall _ -> 2
    | TAppl _ -> 1
;;

(* None = dropped abstraction *)
type typ_context = (string * kind) option list
type term_context = (string * [`OfKind of kind | `OfType of typ]) option list

type typ_former_decl = typ_context * kind
type typ_former_def = typ_former_decl * typ

type term =
  | Rel of int
  | UnitTerm
  | Const of reference
  | Lambda of string * (* typ **) term
  | Appl of term list
  | LetIn of string * (* typ **) term * term
  | Match of reference * term * (term_context * term) list
  | BottomElim
  | TLambda of string * term
  | Inst of (*typ_former **) term
  | Skip of term
  | UnsafeCoerce of term
;;

type term_former_decl = term_context * typ
type term_former_def = term_former_decl * term

let mk_appl f x =
 match f with
    Appl args -> Appl (args@[x])
  | _ -> Appl [f;x]

let mk_tappl f l =
 match f with
    TAppl args -> TAppl (args@l)
  | _ -> TAppl (f::l)

let rec size_of_term =
  function
    | Rel _ -> 1
    | UnitTerm -> 1
    | Const _ -> 1
    | Lambda (_, body) -> 1 + size_of_term body
    | Appl l -> List.length l
    | LetIn (_, def, body) -> 1 + size_of_term def + size_of_term body
    | Match (_, case, pats) -> 1 + size_of_term case + List.length pats
    | BottomElim -> 1
    | TLambda (_,t) -> size_of_term t
    | Inst t -> size_of_term t
    | Skip t -> size_of_term t
    | UnsafeCoerce t -> 1 + size_of_term t
;;

module ReferenceMap = Map.Make(struct type t = Ref.reference let compare = Ref.compare end)

module GlobalNames = Set.Make(String)

type info_el =
 string * [`Type of typ_context * typ option | `Constructor of typ | `Function of typ ]
type info = (Ref.reference * info_el) list
type db = info_el ReferenceMap.t * GlobalNames.t

let empty_info = []

type obj_kind =
   TypeDeclaration of typ_former_decl
 | TypeDefinition of typ_former_def
 | TermDeclaration of term_former_decl
 | TermDefinition of term_former_def
 | LetRec of (info * Ref.reference * obj_kind) list
   (* reference, left, right, constructors *)
 | Algebraic of (info * Ref.reference * typ_context * typ_context * (Ref.reference * typ) list) list

type obj = info * Ref.reference * obj_kind

(* For LetRec and Algebraic blocks *)
let dummyref =
 let uri = NUri.uri_of_string "cic:/matita/dummy/indty.ind" in
 Ref.reference_of_spec uri (Ref.Ind (true,1,1))

type not_term = [`Kind | `KindOrType | `PropKind | `Proposition | `Type];;

let max_not_term t1 t2 =
 match t1,t2 with
    `KindOrType,_
  | _,`KindOrType -> `KindOrType
  | `Kind,_
  | _,`Kind -> `Kind
  | `Type,_
  | _,`Type -> `Type
  | `PropKind,_
  | _,`PropKind -> `PropKind
  | `Proposition,`Proposition -> `Proposition

let sup = List.fold_left max_not_term `Proposition

let rec classify_not_term status context t =
 match NCicReduction.whd status ~subst:[] context t with
  | NCic.Sort s ->
     (match s with
         NCic.Prop
       | NCic.Type [`CProp,_] -> `PropKind
       | NCic.Type [`Type,_] -> `Kind
       | NCic.Type _ -> assert false)
  | NCic.Prod (b,s,t) ->
     (*CSC: using invariant on "_" *)
     classify_not_term status ((b,NCic.Decl s)::context) t
  | NCic.Implicit _
  | NCic.LetIn _
  | NCic.Const (Ref.Ref (_,Ref.CoFix _))
  | NCic.Appl [] ->
     assert false (* NOT POSSIBLE *)
  | NCic.Lambda (n,s,t) ->
     (* Lambdas can me met in branches of matches, expecially when the
        output type is a product *)
     classify_not_term status ((n,NCic.Decl s)::context) t
  | NCic.Match (_,_,_,pl) ->
     let classified_pl = List.map (classify_not_term status context) pl in
      sup classified_pl
  | NCic.Const (Ref.Ref (_,Ref.Fix _)) ->
     assert false (* IMPOSSIBLE *)
  | NCic.Meta _ -> assert false (* TODO *)
  | NCic.Appl (NCic.Const (Ref.Ref (_,Ref.Fix (i,_,_)) as r)::_)->
     let l,_,_ = NCicEnvironment.get_checked_fixes_or_cofixes status r in
     let _,_,_,_,bo = List.nth l i in
      classify_not_term status [] bo
  | NCic.Appl (he::_) -> classify_not_term status context he
  | NCic.Rel n ->
     let rec find_sort typ =
      match NCicReduction.whd status ~subst:[] context (NCicSubstitution.lift status n typ) with
        NCic.Sort NCic.Prop -> `Proposition
      | NCic.Sort (NCic.Type [`CProp,_]) -> `Proposition
      | NCic.Sort (NCic.Type [`Type,_]) ->
         (*CSC: we could be more precise distinguishing the user provided
                minimal elements of the hierarchies and classify these
                as `Kind *)
         `KindOrType
      | NCic.Sort (NCic.Type _) -> assert false (* ALGEBRAIC *)
      | NCic.Prod (_,_,t) ->
         (* we skipped arguments of applications, so here we need to skip
            products *)
         find_sort t
      | _ -> assert false (* NOT A SORT *)
     in
      (match List.nth context (n-1) with
          _,NCic.Decl typ -> find_sort typ
        | _,NCic.Def _ -> assert false (* IMPOSSIBLE *))
  | NCic.Const (Ref.Ref (_,Ref.Decl) as ref) ->
     let _,_,ty,_,_ = NCicEnvironment.get_checked_decl status ref in
      (match classify_not_term status [] ty with
        | `Proposition
        | `Type -> assert false (* IMPOSSIBLE *)
        | `Kind
        | `KindOrType -> `Type
        | `PropKind -> `Proposition)
  | NCic.Const (Ref.Ref (_,Ref.Ind _) as ref) ->
     let _,_,ityl,_,i = NCicEnvironment.get_checked_indtys status ref in
     let _,_,arity,_ = List.nth ityl i in
      (match classify_not_term status [] arity with
        | `Proposition
        | `Type
        | `KindOrType -> assert false (* IMPOSSIBLE *)
        | `Kind -> `Type
        | `PropKind -> `Proposition)
  | NCic.Const (Ref.Ref (_,Ref.Con _))
  | NCic.Const (Ref.Ref (_,Ref.Def _)) ->
     assert false (* IMPOSSIBLE *)
;;

let classify status ~metasenv context t =
 match NCicTypeChecker.typeof status ~metasenv ~subst:[] context t with
  | NCic.Sort _ ->
     (classify_not_term status context t : not_term :> [> not_term])
  | ty ->
     let ty = fix_sorts ty in
      `Term
        (match classify_not_term status context ty with
          | `Proposition -> `Proof
          | `Type -> `Term
          | `KindOrType -> `TypeFormerOrTerm
          | `Kind -> `TypeFormer
          | `PropKind -> `PropFormer)
;;
      

let rec kind_of status ~metasenv context k =
 match NCicReduction.whd status ~subst:[] context k with
  | NCic.Sort NCic.Type _ -> Type
  | NCic.Sort _ -> assert false (* NOT A KIND *)
  | NCic.Prod (b,s,t) ->
     (match classify status ~metasenv context s with
       | `Kind ->
           KArrow (kind_of status ~metasenv context s,
            kind_of ~metasenv status ((b,NCic.Decl s)::context) t)
       | `Type
       | `KindOrType
       | `Proposition
       | `PropKind ->
           KSkip (kind_of status ~metasenv ((b,NCic.Decl s)::context) t)
       | `Term _ -> assert false (* IMPOSSIBLE *))
  | NCic.Implicit _
  | NCic.LetIn _ -> assert false (* IMPOSSIBLE *)
  | NCic.Lambda _
  | NCic.Rel _
  | NCic.Const _ -> assert false (* NOT A KIND *)
  | NCic.Appl _ -> assert false (* TODO: when head is a match/let rec;
                                   otherwise NOT A KIND *)
  | NCic.Meta _
  | NCic.Match (_,_,_,_) -> assert false (* TODO *)
;;

let rec skip_args status ~metasenv context =
 function
  | _,[] -> []
  | [],_ -> assert false (* IMPOSSIBLE *)
  | None::tl1,_::tl2 -> skip_args status ~metasenv context (tl1,tl2)
  | _::tl1,arg::tl2 ->
     match classify status ~metasenv context arg with
      | `KindOrType
      | `Type
      | `Term `TypeFormer ->
         Some arg::skip_args status ~metasenv context (tl1,tl2)
      | `Kind
      | `Proposition
      | `PropKind -> None::skip_args status ~metasenv context (tl1,tl2)
      | `Term _ -> assert false (* IMPOSSIBLE *)
;;

class type g_status =
 object
  method extraction_db: db
 end

class virtual status =
 object
  inherit NCic.status
  val extraction_db = ReferenceMap.empty, GlobalNames.empty
  method extraction_db = extraction_db
  method set_extraction_db v = {< extraction_db = v >}
  method set_extraction_status
   : 'status. #g_status as 'status -> 'self
   = fun o -> {< extraction_db = o#extraction_db >}
 end

let xdo_pretty_print_type = ref (fun _ _ -> assert false)
let do_pretty_print_type status ctx t =
 !xdo_pretty_print_type (status : #status :> status) ctx t

let xdo_pretty_print_term = ref (fun _ _ -> assert false)
let do_pretty_print_term status ctx t =
 !xdo_pretty_print_term (status : #status :> status) ctx t

let term_ctx_of_type_ctx =
 List.map
  (function
      None -> None
    | Some (name,k) -> Some (name,`OfKind k))

let rec split_kind_prods context =
 function
  | KArrow (so,ta)-> split_kind_prods (Some ("_",so)::context) ta
  | KSkip ta -> split_kind_prods (None::context) ta
  | Type -> context,Type
;;

let rec split_typ_prods context =
 function
  | Arrow (so,ta)-> split_typ_prods (Some ("_",`OfType so)::context) ta
  | Forall (name,so,ta)-> split_typ_prods (Some (name,`OfKind so)::context) ta
  | TSkip ta -> split_typ_prods (None::context) ta
  | _ as t -> context,t
;;

let rec glue_ctx_typ ctx typ =
 match ctx with
  | [] -> typ
  | Some (_,`OfType so)::ctx -> glue_ctx_typ ctx (Arrow (so,typ))
  | Some (name,`OfKind so)::ctx -> glue_ctx_typ ctx (Forall (name,so,typ))
  | None::ctx -> glue_ctx_typ ctx (TSkip typ)
;;

let rec split_typ_lambdas status n ~metasenv context typ =
 if n = 0 then context,typ
 else
  match NCicReduction.whd status ~delta:max_int ~subst:[] context typ with
   | NCic.Lambda (name,s,t) ->
      split_typ_lambdas status (n-1) ~metasenv ((name,NCic.Decl s)::context) t
   | t ->
      (* eta-expansion required *)
      let ty = NCicTypeChecker.typeof status ~metasenv ~subst:[] context t in
      match NCicReduction.whd status ~delta:max_int ~subst:[] context ty with
       | NCic.Prod (name,typ,_) ->
          split_typ_lambdas status (n-1) ~metasenv
           ((name,NCic.Decl typ)::context)
           (NCicUntrusted.mk_appl t [NCic.Rel 1])
       | _ -> assert false (* IMPOSSIBLE *)
;;


let rev_context_of_typformer status ~metasenv context =
 function
    NCic.Const (Ref.Ref (_,Ref.Ind _) as ref)
  | NCic.Const (Ref.Ref (_,Ref.Def _) as ref)
  | NCic.Const (Ref.Ref (_,Ref.Decl) as ref)
  | NCic.Const (Ref.Ref (_,Ref.Fix _) as ref) ->
     (try
       match snd (ReferenceMap.find ref (fst status#extraction_db)) with
          `Type (ctx,_) -> List.rev ctx
        | `Constructor _
        | `Function _ -> assert false
      with
       Not_found ->
        (* This can happen only when we are processing the type of
           the constructor of a small singleton type. In this case
           we are not interested in all the type, but only in its
           backbone. That is why we can safely return the dummy context
           here *)
        let rec dummy = None::dummy in
        dummy)
  | NCic.Match _ -> assert false (* TODO ???? *)
  | NCic.Rel n ->
     let typ =
      match List.nth context (n-1) with
         _,NCic.Decl typ -> typ
       | _,NCic.Def _ -> assert false (* IMPOSSIBLE *) in
     let typ_ctx = snd (HExtlib.split_nth n context) in
     let typ = kind_of status ~metasenv typ_ctx typ in
      List.rev (fst (split_kind_prods [] typ))
  | NCic.Meta _ -> assert false (* TODO *)
  | NCic.Const (Ref.Ref (_,Ref.Con _))
  | NCic.Const (Ref.Ref (_,Ref.CoFix _))
  | NCic.Sort _ | NCic.Implicit _ | NCic.Lambda _ | NCic.LetIn _
  | NCic.Appl _ | NCic.Prod _ ->
     assert false (* IMPOSSIBLE *)

let rec typ_of status ~metasenv context k =
 match NCicReduction.whd status ~delta:max_int ~subst:[] context k with
  | NCic.Prod (b,s,t) ->
     (* CSC: non-invariant assumed here about "_" *)
     (match classify status ~metasenv context s with
       | `Kind ->
           Forall (b, kind_of status ~metasenv context s,
            typ_of ~metasenv status ((b,NCic.Decl s)::context) t)
       | `Type
       | `KindOrType -> (* ??? *)
           Arrow (typ_of status ~metasenv context s,
            typ_of status ~metasenv ((b,NCic.Decl s)::context) t)
       | `PropKind
       | `Proposition ->
           TSkip (typ_of status ~metasenv ((b,NCic.Decl s)::context) t)
       | `Term _ -> assert false (* IMPOSSIBLE *))
  | NCic.Sort _
  | NCic.Implicit _
  | NCic.LetIn _ -> assert false (* IMPOSSIBLE *)
  | NCic.Lambda _ -> Top (*assert false (* LAMBDA-LIFT INNER DECLARATION *)*)
  | NCic.Rel n -> Var n
  | NCic.Const ref -> TConst ref
  | NCic.Match (_,_,_,_)
  | NCic.Appl (NCic.Const (Ref.Ref (_,Ref.Fix _))::_) ->
     Top
  | NCic.Appl (he::args) ->
     let rev_he_context= rev_context_of_typformer status ~metasenv context he in
     TAppl (typ_of status ~metasenv context he ::
      List.map
       (function None -> Unit | Some ty -> typ_of status ~metasenv context ty)
       (skip_args status ~metasenv context (rev_he_context,args)))
  | NCic.Appl _ -> assert false (* TODO: when head is a match/let rec;
                                   otherwise NOT A TYPE *)
  | NCic.Meta _ -> assert false (*TODO*)
;;

let rec fomega_lift_type_from n k =
 function
  | Var m as t -> if m < k then t else Var (m + n)
  | Top -> Top
  | TConst _ as t -> t
  | Unit -> Unit
  | Arrow (ty1,ty2) -> Arrow (fomega_lift_type_from n k ty1,fomega_lift_type_from n (k+1) ty2)
  | TSkip t -> TSkip (fomega_lift_type_from n (k+1) t)
  | Forall (name,kind,t) -> Forall (name,kind,fomega_lift_type_from n (k+1) t)
  | TAppl args -> TAppl (List.map (fomega_lift_type_from n k) args)

let fomega_lift_type n t =
 if n = 0 then t else fomega_lift_type_from n 0 t

let fomega_lift_term n t =
 let rec fomega_lift_term n k =
  function
   | Rel m as t -> if m < k then t else Rel (m + n)
   | BottomElim
   | UnitTerm
   | Const _ as t -> t
   | Lambda (name,t) -> Lambda (name,fomega_lift_term n (k+1) t)
   | TLambda (name,t) -> TLambda (name,fomega_lift_term n (k+1) t)
   | Appl args -> Appl (List.map (fomega_lift_term n k) args)
   | LetIn (name,m,bo) ->
      LetIn (name, fomega_lift_term n k m, fomega_lift_term n (k+1) bo)
   | Match (ref,t,pl) ->
      let lift_p (ctx,t) =
       let lift_context ctx =
        let len = List.length ctx in
         HExtlib.list_mapi
          (fun el i ->
            let j = len - i - 1 in
            match el with
               None
             | Some (_,`OfKind  _) as el -> el
             | Some (name,`OfType t) ->
                Some (name,`OfType (fomega_lift_type_from n (k+j) t))
          ) ctx
       in
        lift_context ctx, fomega_lift_term n (k + List.length ctx) t
      in
      Match (ref,fomega_lift_term n k t,List.map lift_p pl)
   | Inst t -> Inst (fomega_lift_term n k t)
   | Skip t -> Skip (fomega_lift_term n (k+1) t)
   | UnsafeCoerce t -> UnsafeCoerce (fomega_lift_term n k t)
 in
  if n = 0 then t else fomega_lift_term n 0 t
;;

let rec fomega_subst k t1 =
 function
  | Var n ->
     if k=n then fomega_lift_type (k-1) t1
     else if n < k then Var n
     else Var (n-1)
  | Top -> Top
  | TConst ref -> TConst ref
  | Unit -> Unit
  | Arrow (ty1,ty2) -> Arrow (fomega_subst k t1 ty1, fomega_subst (k+1) t1 ty2)
  | TSkip t -> TSkip (fomega_subst (k+1) t1 t)
  | Forall (n,kind,t) -> Forall (n,kind,fomega_subst (k+1) t1 t)
  | TAppl (he::args) ->
     mk_tappl (fomega_subst k t1 he) (List.map (fomega_subst k t1) args)
  | TAppl [] -> assert false

let fomega_lookup status ref =
 try
  match snd (ReferenceMap.find ref (fst status#extraction_db)) with
     `Type (_,bo) -> bo
   | `Constructor _
   | `Function _ -> assert false
 with
  Not_found ->
prerr_endline ("BUG, THIS SHOULD NEVER HAPPEN " ^ Ref.string_of_reference ref); None

let rec fomega_whd status ty =
 match ty with
 | TConst r ->
    (match fomega_lookup status r with
        None -> ty
      | Some ty -> fomega_whd status ty)
 | TAppl (TConst r::args) ->
    (match fomega_lookup status r with
        None -> ty
      | Some ty -> fomega_whd status (List.fold_right (fomega_subst 1) args ty))
 | _ -> ty

let rec fomega_conv_kind k1 k2 =
 match k1,k2 with
    Type,Type -> true
  | KArrow (s1,t1), KArrow (s2,t2) ->
     fomega_conv_kind s1 s2 && fomega_conv_kind t1 t2
  | KSkip k1, KSkip k2 -> fomega_conv_kind k1 k2
  | _,_ -> false

let rec fomega_conv status t1 t2 =
 match fomega_whd status t1, fomega_whd status t2 with
    Var n, Var m -> n=m
  | Unit, Unit -> true
  | Top, Top -> true
  | TConst r1, TConst r2 -> Ref.eq r1 r2
  | Arrow (s1,t1), Arrow (s2,t2) ->
     fomega_conv status s1 s2 && fomega_conv status t1 t2
  | TSkip t1, TSkip t2 -> fomega_conv status t1 t2
  | Forall (_,k1,t1), Forall (_,k2,t2) ->
     fomega_conv_kind k1 k2 && fomega_conv status t1 t2
  | TAppl tl1, TAppl tl2 ->
     (try
       List.fold_left2 (fun b t1 t2 -> b && fomega_conv status t1 t2)
        true tl1 tl2
      with
       Invalid_argument _ -> false)
  | _,_ -> false

exception PatchMe (* BUG: constructor of singleton type :-( *)

let type_of_constructor status ref =
 try
  match snd (ReferenceMap.find ref (fst status#extraction_db)) with
     `Constructor ty -> ty
   | _ -> assert false
 with
  Not_found -> raise PatchMe (* BUG: constructor of singleton type :-( *)

let type_of_appl_he status ~metasenv context =
 function
    NCic.Const (Ref.Ref (_,Ref.Con _) as ref)
  | NCic.Const (Ref.Ref (_,Ref.Def _) as ref)
  | NCic.Const (Ref.Ref (_,Ref.Decl) as ref)
  | NCic.Const (Ref.Ref (_,Ref.Fix _) as ref)
  | NCic.Const (Ref.Ref (_,Ref.CoFix _) as ref) ->
     (try
       match snd (ReferenceMap.find ref (fst status#extraction_db)) with
          `Type _ -> assert false
        | `Constructor ty
        | `Function ty -> ty
      with
       Not_found -> assert false)
  | NCic.Const (Ref.Ref (_,Ref.Ind _)) ->
     assert false (* IMPOSSIBLE *)
  | NCic.Rel n ->
     (match List.nth context (n-1) with
         _,NCic.Decl typ
       | _,NCic.Def (_,typ) ->
           (* recomputed every time *)
           typ_of status ~metasenv context
            (NCicSubstitution.lift status n typ))
  | (NCic.Lambda _
  | NCic.LetIn _
  | NCic.Match _) as t ->
     (* BUG: here we should implement a real type-checker since we are
        trusting the translation of the Cic one that could be wrong
        (e.g. pruned abstractions, etc.) *)
     (typ_of status ~metasenv context
      (NCicTypeChecker.typeof status ~metasenv ~subst:[] context t))
  | NCic.Meta _ -> assert false (* TODO *)
  | NCic.Sort _ | NCic.Implicit _ | NCic.Appl _ | NCic.Prod _ ->
     assert false (* IMPOSSIBLE *)

let rec term_of status ~metasenv context =
 function
  | NCic.Implicit _
  | NCic.Sort _
  | NCic.Prod _ -> assert false (* IMPOSSIBLE *)
  | NCic.Lambda (b,ty,bo) ->
     (* CSC: non-invariant assumed here about "_" *)
     (match classify status ~metasenv context ty with
       | `Kind ->
           TLambda (b,term_of status ~metasenv ((b,NCic.Decl ty)::context) bo)
       | `KindOrType (* ??? *)
       | `Type ->
           Lambda (b, term_of status ~metasenv ((b,NCic.Decl ty)::context) bo)
       | `PropKind
       | `Proposition ->
           (* CSC: LAZY ??? *)
           Skip (term_of status ~metasenv ((b,NCic.Decl ty)::context) bo)
       | `Term _ -> assert false (* IMPOSSIBLE *))
  | NCic.LetIn (b,ty,t,bo) ->
     (match classify status ~metasenv context t with
       | `Term `TypeFormerOrTerm (* ???? *)
       | `Term `Term ->
          LetIn (b,term_of status ~metasenv context t,
           term_of status ~metasenv ((b,NCic.Def (t,ty))::context) bo)
       | `Kind
       | `Type
       | `KindOrType
       | `PropKind
       | `Proposition
       | `Term `PropFormer
       | `Term `TypeFormer
       | `Term `Proof ->
         (* not in programming languages, we expand it *)
         term_of status ~metasenv context
          (NCicSubstitution.subst status ~avoid_beta_redexes:true t bo))
  | NCic.Rel n -> Rel n
  | NCic.Const ref -> Const ref
  | NCic.Appl (he::args) ->
     let hety = type_of_appl_he status ~metasenv context he in
      eat_args status metasenv (term_of status ~metasenv context he) context
       hety args
  | NCic.Appl _ -> assert false (* TODO: when head is a match/let rec;
                                   otherwise NOT A TYPE *)
  | NCic.Meta _ -> assert false (* TODO *)
  | NCic.Match (ref,_,t,pl) ->
     let patterns_of pl =
      let _,leftno,_,_,_ = NCicEnvironment.get_checked_indtys status ref in
       let rec eat_branch n ty context ctx pat =
         match (ty, pat) with
         | TSkip t,_
         | Forall (_,_,t),_
         | Arrow (_, t), _ when n > 0 ->
            eat_branch (pred n) t context ctx pat 
         | _, _ when n > 0 -> assert false (*BUG: is Top possible here?*)
         (*CSC: unify the three cases below? *)
         | Arrow (_, t), NCic.Lambda (name, ty, t') ->
           let ctx =
            (Some (name,`OfType (typ_of status ~metasenv context ty)))::ctx in
           let context = (name,NCic.Decl ty)::context in
            eat_branch 0 t context ctx t'
         | Forall (_,_,t),NCic.Lambda (name, ty, t') ->
           let ctx =
            (Some (name,`OfKind (kind_of status ~metasenv context ty)))::ctx in
           let context = (name,NCic.Decl ty)::context in
            eat_branch 0 t context ctx t'
         | TSkip t,NCic.Lambda (name, ty, t') ->
            let ctx = None::ctx in
            let context = (name,NCic.Decl ty)::context in
             eat_branch 0 t context ctx t'
         | Top,_ -> assert false (* IMPOSSIBLE *)
         | TSkip _, _
         | Forall _,_
         | Arrow _,_ -> assert false (*BUG here, eta-expand!*)
         | _, _ -> context,ctx, pat
       in
        try
         HExtlib.list_mapi
          (fun pat i ->
            let ref = Ref.mk_constructor (i+1) ref in
            let ty = 
             (* BUG HERE, QUICK BUG WRONG PATCH IN PLACE *)
             try
              type_of_constructor status ref
             with
              PatchMe ->
               typ_of status ~metasenv context
                (NCicTypeChecker.typeof status ~metasenv ~subst:[] context
                 (NCic.Const ref))
            in
            let context,lhs,rhs = eat_branch leftno ty context [] pat in
            let rhs =
             (* UnsafeCoerce not always required *)
             UnsafeCoerce (term_of status ~metasenv context rhs)
            in
             lhs,rhs
          ) pl
        with Invalid_argument _ -> assert false
     in
     (match classify_not_term status [] (NCic.Const ref) with
      | `PropKind
      | `KindOrType
      | `Kind -> assert false (* IMPOSSIBLE *)
      | `Proposition ->
          (match patterns_of pl with
              [] -> BottomElim
            | [lhs,rhs] -> fomega_lift_term (- List.length lhs) rhs
            | _ -> assert false)
      | `Type ->
          Match (ref,term_of status ~metasenv context t, patterns_of pl))
and eat_args status metasenv acc context tyhe =
 function
    [] -> acc
  | arg::tl ->
     match fomega_whd status tyhe with
        Arrow (s,t) ->
         let acc =
          match s with
             Unit -> mk_appl acc UnitTerm
           | _ ->
             let foarg = term_of status ~metasenv context arg in
              (* BUG HERE, we should implement a real type-checker instead of
                 trusting the Cic type *)
             let inferredty =
              typ_of status ~metasenv context
               (NCicTypeChecker.typeof status ~metasenv ~subst:[] context arg)in
              if fomega_conv status inferredty s then
               mk_appl acc foarg
              else
(
prerr_endline ("ARG = " ^ status#ppterm ~metasenv ~subst:[] ~context arg);
let context = List.map fst context in
prerr_endline ("HE = " ^ do_pretty_print_term status context acc);
prerr_endline ("CONTEXT= " ^ String.concat " " context);
prerr_endline ("NOT CONV: " ^ do_pretty_print_type status context inferredty ^ " vs " ^ do_pretty_print_type status context s);
               mk_appl acc (UnsafeCoerce foarg)
)
         in
          eat_args status metasenv acc context (fomega_subst 1 Unit t) tl
      | Top ->
         let arg =
          match classify status ~metasenv context arg with
           | `PropKind
           | `Proposition
           | `Term `TypeFormer
           | `Term `PropFormer
           | `Term `Proof
           | `Type
           | `KindOrType
           | `Kind -> UnitTerm
           | `Term `TypeFormerOrTerm
           | `Term `Term -> term_of status ~metasenv context arg
         in
          (* BUG: what if an argument of Top has been erased??? *)
          eat_args status metasenv
           (UnsafeCoerce (mk_appl acc (UnsafeCoerce arg)))
           context Top tl
      | Forall (_,_,t) ->
(*
prerr_endline "FORALL";
let xcontext = List.map fst context in
prerr_endline ("TYPE: " ^ do_pretty_print_type status xcontext (fomega_whd status tyhe));
prerr_endline ("fARG = " ^ status#ppterm ~metasenv ~subst:[] ~context arg);
prerr_endline ("fHE = " ^ do_pretty_print_term status xcontext acc);
prerr_endline ("fCONTEXT= " ^ String.concat " " xcontext);
*)
         (match classify status ~metasenv context arg with
           | `PropKind -> assert false (*TODO: same as below, coercion needed???*)
           | `Proposition
           | `Kind ->
               eat_args status metasenv (UnsafeCoerce (Inst acc))
                context (fomega_subst 1 Unit t) tl
           | `KindOrType
           | `Term `TypeFormer
           | `Type ->
               eat_args status metasenv (Inst acc)
                context (fomega_subst 1 (typ_of status ~metasenv context arg) t)
                 tl
           | `Term _ -> assert false (*TODO: ????*))
      | TSkip t ->
         eat_args status metasenv acc context t tl
      | Unit | Var _ | TConst _ | TAppl _ -> assert false (* NOT A PRODUCT *)
;;

type 'a result =
  | Erased
  | OutsideTheory
  | Failure of string
  | Success of 'a
;;

let fresh_name_of_ref status ref =
 (*CSC: Patch while we wait for separate compilation *)
 let candidate =
  let name = NCicPp.r2s status true ref in
  let Ref.Ref (uri,_) = ref in
  let path = NUri.baseuri_of_uri uri in
  let path = String.sub path 5 (String.length path - 5) in
  let path = Str.global_replace (Str.regexp "/") "_" path in
   path ^ "_" ^ name
 in
 let rec freshen candidate =
  if GlobalNames.mem candidate (snd status#extraction_db) then
   freshen (candidate ^ "'")
  else
   candidate
 in
  freshen candidate

let register_info (db,names) (ref,(name,_ as info_el)) =
 ReferenceMap.add ref info_el db,GlobalNames.add name names

let register_name_and_info status (ref,info_el) =
 let name = fresh_name_of_ref status ref in
 let info = ref,(name,info_el) in
 let infos,names = status#extraction_db in
  status#set_extraction_db (register_info (infos,names) info), info

let register_infos = List.fold_left register_info

let object_of_constant status ~metasenv ref bo ty =
  match classify status ~metasenv [] ty with
    | `Kind ->
        let ty = kind_of status ~metasenv [] ty in
        let ctx0,res = split_kind_prods [] ty in
        let ctx,bo =
         split_typ_lambdas status ~metasenv (List.length ctx0) [] bo in
        (match classify status ~metasenv ctx bo with
          | `Type
          | `KindOrType -> (* ?? no kind formers in System F_omega *)
              let nicectx =
               List.map2
                (fun p1 n ->
                  HExtlib.map_option (fun (_,k) ->
                   (*CSC: BUG here, clashes*)
                   String.uncapitalize (fst n),k) p1)
                ctx0 ctx
              in
              let bo = typ_of status ~metasenv ctx bo in
              let info = ref,`Type (nicectx,Some bo) in
              let status,info = register_name_and_info status info in
               status,Success ([info],ref,TypeDefinition((nicectx,res),bo))
          | `Kind -> status, Erased (* DPM: but not really, more a failure! *)
          | `PropKind
          | `Proposition -> status, Erased
          | `Term _ -> status, Failure "Body of type lambda classified as a term.  This is a bug.")
    | `PropKind
    | `Proposition -> status, Erased
    | `KindOrType (* ??? *)
    | `Type ->
       let ty = typ_of status ~metasenv [] ty in
       let info = ref,`Function ty in
       let status,info = register_name_and_info status info in
        status,
         Success ([info],ref, TermDefinition (split_typ_prods [] ty,
         term_of status ~metasenv [] bo))
    | `Term _ -> status, Failure "Non-term classified as a term.  This is a bug."
;;

let object_of_inductive status ~metasenv uri ind leftno il =
 let status,_,rev_tyl =
  List.fold_left
   (fun (status,i,res) (_,_,arity,cl) ->
     match classify_not_term status [] arity with
      | `Proposition
      | `KindOrType
      | `Type -> assert false (* IMPOSSIBLE *)
      | `PropKind -> status,i+1,res
      | `Kind ->
          let arity = kind_of status ~metasenv [] arity in
          let ctx,_ = split_kind_prods [] arity in
          let right,left = HExtlib.split_nth (List.length ctx - leftno) ctx in
          let ref =
           Ref.reference_of_spec uri (Ref.Ind (ind,i,leftno)) in
          let info = ref,`Type (ctx,None) in
          let status,info = register_name_and_info status info in
          let _,status,cl_rev,infos =
           List.fold_left
            (fun (j,status,res,infos) (_,_,ty) ->
              let ctx,ty =
               NCicReduction.split_prods status ~subst:[] [] leftno ty in
              let ty = typ_of status ~metasenv ctx ty in
              let left = term_ctx_of_type_ctx left in
              let full_ty = glue_ctx_typ left ty in
              let ref = Ref.mk_constructor j ref in
              let info = ref,`Constructor full_ty in
              let status,info = register_name_and_info status info in
               j+1,status,((ref,ty)::res),info::infos
            ) (1,status,[],[]) cl
          in
           status,i+1,(info::infos,ref,left,right,List.rev cl_rev)::res
   ) (status,0,[]) il
 in
  match rev_tyl with
     [] -> status,Erased
   | _ -> status, Success ([], dummyref, Algebraic (List.rev rev_tyl))
;;

let object_of status (uri,height,metasenv,subst,obj_kind) =
  let obj_kind = apply_subst subst obj_kind in
      match obj_kind with
        | NCic.Constant (_,_,None,ty,_) ->
          let ref = Ref.reference_of_spec uri Ref.Decl in
          (match classify status ~metasenv [] ty with
            | `Kind ->
              let ty = kind_of status ~metasenv [] ty in
              let ctx,_ as res = split_kind_prods [] ty in
              let info = ref,`Type (ctx,None) in
              let status,info = register_name_and_info status info in
               status, Success ([info],ref, TypeDeclaration res)
            | `PropKind
            | `Proposition -> status, Erased
            | `Type
            | `KindOrType (*???*) ->
              let ty = typ_of status ~metasenv [] ty in
              let info = ref,`Function ty in
              let status,info = register_name_and_info status info in
               status,Success ([info],ref,
                TermDeclaration (split_typ_prods [] ty))
            | `Term _ -> status, Failure "Type classified as a term.  This is a bug.")
        | NCic.Constant (_,_,Some bo,ty,_) ->
           let ref = Ref.reference_of_spec uri (Ref.Def height) in
            object_of_constant status ~metasenv ref bo ty
        | NCic.Fixpoint (fix_or_cofix,fs,_) ->
          let _,status,objs =
            List.fold_right
            (fun (_,_name,recno,ty,bo) (i,status,res) ->
              let ref =
               if fix_or_cofix then
                Ref.reference_of_spec
                 uri (Ref.Fix (i,recno,height))
               else
                Ref.reference_of_spec uri (Ref.CoFix i)
              in
              let status,obj = object_of_constant ~metasenv status ref bo ty in
                match obj with
                  | Success (info,ref,obj) -> i+1,status, (info,ref,obj)::res
                  | _ -> i+1,status, res) fs (0,status,[])
          in
            status, Success ([],dummyref,LetRec objs)
        | NCic.Inductive (ind,leftno,il,_) ->
           object_of_inductive status ~metasenv uri ind leftno il

(************************ HASKELL *************************)

(* -----------------------------------------------------------------------------
 * Helper functions I can't seem to find anywhere in the OCaml stdlib?
 * -----------------------------------------------------------------------------
 *)
let (|>) f g =
  fun x -> g (f x)
;;

let curry f x y =
  f (x, y)
;;

let uncurry f (x, y) =
  f x y
;;

let rec char_list_of_string s =
  let l = String.length s in
  let rec aux buffer s =
    function
      | 0 -> buffer
      | m -> aux (s.[m - 1]::buffer) s (m - 1)
  in
    aux [] s l
;;

let string_of_char_list s =
  let rec aux buffer =
    function
      | []    -> buffer
      | x::xs -> aux (String.make 1 x ^ buffer) xs
  in
    aux "" s
;;

(* ----------------------------------------------------------------------------
 * Haskell name management: prettyfying valid and idiomatic Haskell identifiers
 * and type variable names.
 * ----------------------------------------------------------------------------
 *)

let remove_underscores_and_mark l =
  let rec aux char_list_buffer positions_buffer position =
    function
      | []    -> (string_of_char_list char_list_buffer, positions_buffer)
      | x::xs ->
        if x == '_' then
          aux char_list_buffer (position::positions_buffer) position xs
        else
          aux (x::char_list_buffer) positions_buffer (position + 1) xs
  in
   if l = ['_'] then "_",[] else aux [] [] 0 l
;;

let rec capitalize_marked_positions s =
  function
    | []    -> s
    | x::xs ->
      if x < String.length s then
        let c = Char.uppercase (String.get s x) in
        let _ = String.set s x c in
          capitalize_marked_positions s xs
      else
        capitalize_marked_positions s xs
;;

let contract_underscores_and_capitalise =
  char_list_of_string |>
  remove_underscores_and_mark |>
  uncurry capitalize_marked_positions
;;

let idiomatic_haskell_type_name_of_string =
  contract_underscores_and_capitalise |>
  String.capitalize
;;

let idiomatic_haskell_term_name_of_string =
  contract_underscores_and_capitalise |>
  String.uncapitalize
;;

let classify_reference status ref =
 try
  match snd (ReferenceMap.find ref (fst status#extraction_db)) with
     `Type _ -> `TypeName
   | `Constructor _ -> `Constructor
   | `Function _ -> `FunctionName
 with
  Not_found ->
prerr_endline ("BUG, THIS SHOULD NEVER HAPPEN " ^ Ref.string_of_reference ref); `FunctionName
;;

let capitalize classification name =
  match classification with
    | `Constructor
    | `TypeName -> idiomatic_haskell_type_name_of_string name
    | `TypeVariable
    | `BoundVariable
    | `FunctionName -> idiomatic_haskell_term_name_of_string name
;;

let pp_ref status ref =
 capitalize (classify_reference status ref)
  (try fst (ReferenceMap.find ref (fst status#extraction_db))
   with Not_found ->
prerr_endline ("BUG with coercions: " ^ Ref.string_of_reference ref);
(*assert false*)
 NCicPp.r2s status true ref (* BUG: this should never happen *)
)

(* cons avoid duplicates *)
let rec (@:::) name l =
 if name <> "" (* propositional things *) && name.[0] = '_' then
  let name = String.sub name 1 (String.length name - 1) in
  let name = if name = "" then "a" else name in
   name @::: l
 else if List.mem name l then (name ^ "'") @::: l
 else name,l
;;

let (@::) x l = let x,l = x @::: l in x::l;;

let rec pretty_print_type status ctxt =
  function
    | Var n -> List.nth ctxt (n-1)
    | Unit -> "()"
    | Top -> "GHC.Prim.Any"
    | TConst ref -> pp_ref status ref
    | Arrow (t1,t2) ->
        bracket size_of_type (pretty_print_type status ctxt) t1 ^ " -> " ^
         pretty_print_type status ("_"::ctxt) t2
    | TSkip t -> pretty_print_type status ("_"::ctxt) t
    | Forall (name, kind, t) ->
      (*CSC: BUG HERE: avoid clashes due to uncapitalisation*)
      let name = capitalize `TypeVariable name in
      let name,ctxt = name@:::ctxt in
        if size_of_kind kind > 1 then
          "forall (" ^ name ^ " :: " ^ pretty_print_kind kind ^ "). " ^ pretty_print_type status (name::ctxt) t
        else
          "forall " ^ name ^ ". " ^ pretty_print_type status (name::ctxt) t
   | TAppl tl ->
      String.concat " "
       (List.map
         (fun t -> bracket ~prec:0 size_of_type
          (pretty_print_type status ctxt) t) tl)
;;

xdo_pretty_print_type := pretty_print_type;;


let pretty_print_term_context status ctx1 ctx2 =
 let name_context, rev_res =
  List.fold_right
    (fun el (ctx1,rev_res) ->
      match el with
         None -> ""@::ctx1,rev_res
       | Some (name,`OfKind _) ->
          let name = capitalize `TypeVariable name in
           name@::ctx1,rev_res
       | Some (name,`OfType typ) ->
          let name = capitalize `TypeVariable name in
          let name,ctx1 = name@:::ctx1 in
           name::ctx1,
            ("(" ^ name ^ " :: " ^ pretty_print_type status ctx1 typ ^ ")")::rev_res
    ) ctx2 (ctx1,[]) in
  name_context, String.concat " " (List.rev rev_res)

let rec pretty_print_term status ctxt =
  function
    | Rel n -> List.nth ctxt (n-1)
    | UnitTerm -> "()"
    | Const ref -> pp_ref status ref
    | Lambda (name,t) ->
       let name = capitalize `BoundVariable name in
       let name,ctxt = name@:::ctxt in
        "\\" ^ name ^ " -> " ^ pretty_print_term status (name::ctxt) t
    | Appl tl -> String.concat " " (List.map (bracket size_of_term (pretty_print_term status ctxt)) tl)
    | LetIn (name,s,t) ->
       let name = capitalize `BoundVariable name in
       let name,ctxt = name@:::ctxt in
        "let " ^ name ^ " = " ^ pretty_print_term status ctxt s ^ " in " ^
         pretty_print_term status (name::ctxt) t
    | BottomElim ->
       "error \"Unreachable code\""
    | UnsafeCoerce t ->
       "unsafeCoerce " ^ bracket size_of_term (pretty_print_term status ctxt) t
    | Match (r,matched,pl) ->
      if pl = [] then
       "error \"Case analysis over empty type\""
      else
       "case " ^ pretty_print_term status ctxt matched ^ " of {\n" ^
         String.concat " ;\n"
           (HExtlib.list_mapi
             (fun (bound_names,rhs) i ->
               let ref = Ref.mk_constructor (i+1) r in
               let name = pp_ref status ref in
               let ctxt,bound_names =
                pretty_print_term_context status ctxt bound_names in
               let body =
                pretty_print_term status ctxt rhs
               in
                 "  " ^ name ^ " " ^ bound_names ^ " -> " ^ body
             ) pl) ^ "}\n  "
    | Skip t -> pretty_print_term status ("[[skipped]]"@::ctxt) t
    | TLambda (name,t) ->
       let name = capitalize `TypeVariable name in
        pretty_print_term status (name@::ctxt) t
    | Inst t -> pretty_print_term status ctxt t
;;

xdo_pretty_print_term := pretty_print_term;;

let rec pp_obj status (_,ref,obj_kind) =
  let pretty_print_context ctx =
    String.concat " " (List.rev (snd
      (List.fold_right
       (fun (x,kind) (l,res) ->
         let x,l = x @:::l in
         if size_of_kind kind > 1 then
          x::l,("(" ^ x ^ " :: " ^ pretty_print_kind kind ^ ")")::res
         else
          x::l,x::res)
       (HExtlib.filter_map (fun x -> x) ctx) ([],[]))))
  in
 let namectx_of_ctx ctx =
  List.fold_right (@::)
   (List.map (function None -> "" | Some (x,_) -> x) ctx) [] in
 match obj_kind with
   TypeDeclaration (ctx,_) ->
    (* data?? unsure semantics: inductive type without constructor, but
       not matchable apparently *)
    if List.length ctx = 0 then
      "data " ^ pp_ref status ref
    else
      "data " ^ pp_ref status ref ^ " " ^ pretty_print_context ctx
 | TypeDefinition ((ctx, _),ty) ->
    let namectx = namectx_of_ctx ctx in
    if List.length ctx = 0 then
      "type " ^ pp_ref status ref ^ " = " ^ pretty_print_type status namectx ty
    else
      "type " ^ pp_ref status ref ^ " " ^ pretty_print_context ctx ^ " = " ^ pretty_print_type status namectx ty
 | TermDeclaration (ctx,ty) ->
    let name = pp_ref status ref in
      name ^ " :: " ^ pretty_print_type status [] (glue_ctx_typ ctx ty) ^ "\n" ^
      name ^ " = error \"The declaration `" ^ name ^ "' has yet to be defined.\""
 | TermDefinition ((ctx,ty),bo) ->
    let name = pp_ref status ref in
    let namectx = namectx_of_ctx ctx in
    (*CSC: BUG here *)
    name ^ " :: " ^ pretty_print_type status namectx (glue_ctx_typ ctx ty) ^ "\n" ^
    name ^ " = " ^ pretty_print_term status namectx bo
 | LetRec l ->
    String.concat "\n" (List.map (pp_obj status) l)
 | Algebraic il ->
    String.concat "\n"
     (List.map
      (fun _,ref,left,right,cl ->
        "data " ^ pp_ref status ref ^ " " ^
        pretty_print_context (right@left) ^ " where\n  " ^
        String.concat "\n  " (List.map
         (fun ref,tys ->
           let namectx = namectx_of_ctx left in
            pp_ref status ref ^ " :: " ^
             pretty_print_type status namectx tys
         ) cl) (*^ "\n    deriving (Prelude.Show)"*)
      ) il)
 (* inductive and records missing *)

let rec infos_of (info,_,obj_kind) =
 info @
  match obj_kind with
     LetRec l -> List.concat (List.map (fun (infos,_,_) -> infos) l)
   | Algebraic l -> List.concat (List.map (fun (infos,_,_,_,_) -> infos) l)
   | _ -> []

let haskell_of_obj status (uri,_,_,_,_ as obj) =
 let status, obj = object_of status obj in
  status,
   match obj with
      Erased -> "-- [?] " ^ NUri.name_of_uri uri ^ " erased due to term being propositionally irrelevant.\n",[]
    | OutsideTheory -> "-- [?] " ^ NUri.name_of_uri uri ^ " erased due to image of term under extraction residing outside Fω.\n",[]
    | Failure msg -> "-- [?] " ^ NUri.name_of_uri uri ^ " FAILURE: " ^ msg ^ "\n",[]
    | Success o -> pp_obj status o ^ "\n", infos_of o

let refresh_uri_in_typ ~refresh_uri_in_reference =
 let rec refresh_uri_in_typ =
  function
   | Var _
   | Unit
   | Top as t -> t
   | TConst r -> TConst (refresh_uri_in_reference r)
   | Arrow (t1,t2) -> Arrow (refresh_uri_in_typ t1, refresh_uri_in_typ t2)
   | TSkip t -> TSkip (refresh_uri_in_typ t)
   | Forall (n,k,t) -> Forall (n,k,refresh_uri_in_typ t)
   | TAppl tl -> TAppl (List.map refresh_uri_in_typ tl)
 in
  refresh_uri_in_typ

let refresh_uri_in_info ~refresh_uri_in_reference infos =
 List.map
  (function (ref,el) ->
    match el with
       name,`Constructor typ ->
        let typ = refresh_uri_in_typ ~refresh_uri_in_reference typ in
         refresh_uri_in_reference ref, (name,`Constructor typ)
     | name,`Function typ ->
        let typ = refresh_uri_in_typ ~refresh_uri_in_reference typ in
         refresh_uri_in_reference ref, (name,`Function typ)
     | name,`Type (ctx,typ) ->
         let typ =
          match typ with
             None -> None
           | Some t -> Some (refresh_uri_in_typ ~refresh_uri_in_reference t)
         in
          refresh_uri_in_reference ref, (name,`Type (ctx,typ)))
  infos
