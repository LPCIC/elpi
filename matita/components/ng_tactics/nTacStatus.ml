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

let debug = ref false;;
let pp x = 
 if !debug then prerr_endline (Lazy.force x) else ()
;;

type automation_cache = NDiscriminationTree.DiscriminationTree.t
type unit_eq_cache = NCicParamod.state

exception Error of string lazy_t * exn option
let fail ?exn msg = raise (Error (msg,exn))

module NRef = NReference

let wrap fname f x =
  try f x 
  with 
  | MultiPassDisambiguator.DisambiguationError _ 
  | NCicRefiner.RefineFailure _ 
  | NCicRefiner.Uncertain _ 
  | NCicUnification.UnificationFailure _ 
  | NCicUnification.Uncertain _ 
  | NCicTypeChecker.TypeCheckerFailure _ 
  | NCicMetaSubst.MetaSubstFailure _
  | NCicMetaSubst.Uncertain _ as exn -> fail ~exn (lazy fname)
;;

class type g_eq_status =
 object
   method eq_cache : unit_eq_cache 
 end

class eq_status =
 object(self)
  val eq_cache = NCicParamod.empty_state
  method eq_cache = eq_cache
  method set_eq_cache v = {< eq_cache = v >}
  method set_eq_status
   : 'status. #g_eq_status as 'status -> 'self
   = fun o -> self#set_eq_cache o#eq_cache
 end

class type g_auto_status =
 object
   method auto_cache : automation_cache
 end

class auto_status =
 object(self)
  val auto_cache = NDiscriminationTree.DiscriminationTree.empty
  method auto_cache = auto_cache
  method set_auto_cache v = {< auto_cache = v >}
  method set_auto_status
   : 'status. #g_auto_status as 'status -> 'self
   = fun o -> self#set_auto_cache o#auto_cache
 end

class type g_pstatus =
 object
  inherit GrafiteDisambiguate.g_status
  inherit g_auto_status
  inherit g_eq_status
  method obj: NCic.obj
 end

class virtual pstatus =
 fun (o: NCic.obj) ->
 object (self)
   inherit GrafiteDisambiguate.status
   inherit auto_status
   inherit eq_status
   val obj = o
   method obj = obj
   method set_obj o = {< obj = o >}
   method set_pstatus : 'status. #g_pstatus as 'status -> 'self
   = fun o ->
    (((self#set_disambiguate_status o)#set_obj o#obj)#set_auto_status o)#set_eq_status o
  end

type tactic_term = NotationPt.term Disambiguate.disambiguator_input
type tactic_pattern = GrafiteAst.npattern Disambiguate.disambiguator_input

type cic_term = NCic.context * NCic.term
let ctx_of (c,_) = c ;;
let mk_cic_term c t = c,t ;;

let ppterm (status:#pstatus) t =
 let uri,height,metasenv,subst,obj = status#obj in
 let context,t = t in
  status#ppterm ~metasenv ~subst ~context t
;;

let ppcontext (status: #pstatus) c =
 let uri,height,metasenv,subst,obj = status#obj in
  status#ppcontext ~metasenv ~subst c
;;

let ppterm_and_context (status: #pstatus) t =
 let uri,height,metasenv,subst,obj = status#obj in
 let context,t = t in
  status#ppcontext ~metasenv ~subst context ^ "\n ⊢ "^ 
  status#ppterm ~metasenv ~subst ~context t
;;

let relocate status destination (source,t as orig) =
 pp(lazy("relocate:\n" ^ ppterm_and_context status orig));
 pp(lazy("relocate in:\n" ^ ppcontext status destination));
 let rc = 
   if source == destination then status, orig else
    let _, _, metasenv, subst, _ = status#obj in
    let rec compute_ops ctx = function (* destination, source *)
      | (n1, NCic.Decl t1 as e)::cl1 as ex, (n2, NCic.Decl t2)::cl2 ->
          if n1 = n2 && 
             NCicReduction.are_convertible status ctx ~subst ~metasenv t1 t2 then
            compute_ops (e::ctx) (cl1,cl2)
          else
            [ `Delift ctx; `Lift (List.rev ex) ]
      | (n1, NCic.Def (b1,t1) as e)::cl1 as ex, (n2, NCic.Def (b2,t2))::cl2 ->
          if n1 = n2 && 
             NCicReduction.are_convertible status ctx ~subst ~metasenv t1 t2 &&
             NCicReduction.are_convertible status ctx ~subst ~metasenv b1 b2 then
            compute_ops (e::ctx) (cl1,cl2)
          else
            [ `Delift ctx; `Lift (List.rev ex) ]
      | (n1, NCic.Def (b1,t1) as e)::cl1 as ex, (n2, NCic.Decl t2)::cl2 ->
          if n1 = n2 && 
             NCicReduction.are_convertible status ctx ~subst ~metasenv t1 t2 then
            compute_ops (e::ctx) (cl1,cl2)
          else
            [ `Delift ctx; `Lift (List.rev ex) ]
      | (n1, NCic.Decl _)::cl1 as ex, (n2, NCic.Def _)::cl2 -> 
            [ `Delift ctx; `Lift (List.rev ex) ]
      | _::_ as ex, [] -> [ `Lift (List.rev ex) ]
      | [], _::_ -> [ `Delift ctx ]
      | [],[] -> []
    in
    let ops = compute_ops [] (List.rev destination, List.rev source) in
    let rec mk_irl i j = if i > j then [] else NCic.Rel i :: mk_irl (i+1) j in
    List.fold_left 
     (fun (status, (source,t)) -> function 
      | `Lift extra_ctx -> 
           let len = List.length extra_ctx in
           status, (extra_ctx@source, NCicSubstitution.lift status len t)
      | `Delift ctx -> 
            let len_ctx = List.length ctx in
            let irl = mk_irl 1 (List.length ctx) in
            let lc = List.length source - len_ctx, NCic.Ctx irl in
            let u, d, metasenv, subst, o = status#obj in
            pp(lazy("delifting as " ^ 
              status#ppterm ~metasenv ~subst ~context:source 
               (NCic.Meta (-1,lc))));
            let (metasenv, subst), t =
              NCicMetaSubst.delift status
                 ~unify:(fun m s c t1 t2 -> 
                   try Some (NCicUnification.unify status m s c t1 t2)
                   with 
                    | NCicUnification.UnificationFailure _ 
                    | NCicUnification.Uncertain _ -> None) 
               metasenv subst source (-1) lc t
            in
            let status = status#set_obj (u, d, metasenv, subst, o) in
            status, (ctx,t))
       (status,orig) ops
 in
 pp(lazy("relocated: " ^ ppterm (fst rc) (snd rc)));
 rc
;;
let relocate a b c = wrap "relocate" (relocate a b) c;;

let term_of_cic_term s t c = 
  let s, (_,t) = relocate s c t in
  s, t
;;

let disambiguate status context t ty =
 let status, expty = 
   match ty with 
   | `XTSome ty -> 
       let status, (_,x) = relocate status context ty in status, `XTSome x 
   | `XTNone -> status, `XTNone 
   | `XTSort -> status, `XTSort
   | `XTInd  -> status, `XTInd
 in
 let uri,height,metasenv,subst,obj = status#obj in
 let metasenv, subst, status, t = 
   GrafiteDisambiguate.disambiguate_nterm status expty context metasenv subst t 
 in
 let new_pstatus = uri,height,metasenv,subst,obj in
  status#set_obj new_pstatus, (context, t) 
;;
let disambiguate a b c d = wrap "disambiguate" (disambiguate a b c) d;;

let typeof status ctx t =
  let status, (_,t) = relocate status ctx t in
  let _,_,metasenv,subst,_ = status#obj in
  let ty = NCicTypeChecker.typeof status ~subst ~metasenv ctx t in
  status, (ctx, ty)
;;
let typeof a b c = wrap "typeof" (typeof a b) c;;

let saturate status ?delta (ctx,t) =
  let n,h,metasenv,subst,k = status#obj in
  let t,metasenv,args = NCicMetaSubst.saturate status ?delta metasenv subst ctx t 0 in
  let status = status#set_obj (n,h,metasenv,subst,k) in
  status, (ctx,t), List.map (fun x -> ctx,x) args
;;
let saturate a ?delta b = wrap "saturate" (saturate a ?delta) b;;
  
let whd status ?delta ctx t =
  let status, (_,t) = relocate status ctx t in
  let _,_,_,subst,_ = status#obj in
  let t = NCicReduction.whd status ~subst ?delta ctx t in
  status, (ctx, t)
;;
  
let normalize status ?delta ctx t =
  let status, (_,t) = relocate status ctx t in
  let _,_,_,subst,_ = status#obj in
  let t = NCicTacReduction.normalize status ~subst ?delta ctx t in
  status, (ctx, t)
;;
  
let unify status ctx a b =
  let status, (_,a) = relocate status ctx a in
  let status, (_,b) = relocate status ctx b in
  let n,h,metasenv,subst,o = status#obj in
  let metasenv, subst = NCicUnification.unify status metasenv subst ctx a b in
   status#set_obj (n,h,metasenv,subst,o)
;;
let unify a b c d = wrap "unify" (unify a b c) d;;

let fix_sorts status (ctx,t) =
 let f () =
  let name,height,metasenv,subst,obj = status#obj in
  let metasenv, t = 
    NCicUnification.fix_sorts status metasenv subst t in
  let status = status#set_obj (name,height,metasenv,subst,obj) in
   status, (ctx,t)
 in
  wrap "fix_sorts" f ()
;;

let refine status ctx term expty =
  let status, (_,term) = relocate status ctx term in
  let status, expty = 
    match expty with
    | `XTSome e -> 
        let status, (_, e) = relocate status ctx e in status, `XTSome e
    | `XTNone -> status, `XTNone 
    | `XTSort -> status, `XTSort
    | `XTInd  -> status, `XTInd
  in
  let name,height,metasenv,subst,obj = status#obj in
  let metasenv,subst,t,ty = 
   NCicRefiner.typeof status metasenv subst ctx term expty
  in
   status#set_obj (name,height,metasenv,subst,obj), (ctx,t), (ctx,ty)
;;
let refine a b c d = wrap "refine" (refine a b c) d;;

let get_goalty status g =
 let _,_,metasenv,_,_ = status#obj in
 try
   let _, ctx, ty = NCicUtils.lookup_meta g metasenv in
   ctx, ty
 with NCicUtils.Meta_not_found _ as exn -> fail ~exn (lazy "get_goalty")
;;

let get_subst status =
  let _,_,_,subst,_ = status#obj in subst
;;

let to_subst status i entry =
 let name,height,metasenv,subst,obj = status#obj in
 let metasenv = List.filter (fun j,_ -> j <> i) metasenv in
 let subst = (i, entry) :: subst in
  status#set_obj (name,height,metasenv,subst,obj)
;;

let instantiate status ?refine:(dorefine=true) i t =
 let _,_,metasenv,_,_ = status#obj in
 let gname, context, gty = List.assoc i metasenv in
  if dorefine then
   let status, (_,t), (_,ty) = refine status context t (`XTSome (context,gty)) in
    to_subst status i (gname,context,t,ty)
  else
   let status,(_,ty) = typeof status context t in
    to_subst status i (gname,context,snd t,ty)
;;

let instantiate_with_ast status i t =
 let _,_,metasenv,_,_ = status#obj in
 let gname, context, gty = List.assoc i metasenv in
 let ggty = mk_cic_term context gty in
 let status, (_,t) = disambiguate status context t (`XTSome ggty) in
  to_subst status i (gname,context,t,gty)
;;

let mk_meta status ?(attrs=[]) ctx bo_or_ty kind =
  match bo_or_ty with
  | `Decl ty ->
      let status, (_,ty) = relocate status ctx ty in
      let n,h,metasenv,subst,o = status#obj in
      let metasenv, _, instance, _ = 
        NCicMetaSubst.mk_meta ~attrs metasenv ctx ~with_type:ty kind
      in
      let status = status#set_obj (n,h,metasenv,subst,o) in
      status, (ctx,instance)
  | `Def bo ->
      let status, (_,bo_ as bo) = relocate status ctx bo in
      let status, (_,ty) = typeof status ctx bo in
      let n,h,metasenv,subst,o = status#obj in
      let metasenv, metano, instance, _ = 
        NCicMetaSubst.mk_meta ~attrs metasenv ctx ~with_type:ty kind in
      let attrs,_,_ = NCicUtils.lookup_meta metano metasenv in
      let metasenv = List.filter (fun j,_ -> j <> metano) metasenv in
      let subst = (metano, (attrs, ctx, bo_, ty)) :: subst in
      let status = status#set_obj (n,h,metasenv,subst,o) in
      status, (ctx,instance)
;;

let mk_in_scope status t =
  mk_meta status ~attrs:[`InScope] (ctx_of t) (`Def t) `IsTerm
;;

let mk_out_scope n status t = 
  mk_meta status ~attrs:[`OutScope n] (ctx_of t) (`Def t) `IsTerm
;;

(* the following unification problem will be driven by 
 *   select s ~found:mk_in_scope ~postprocess:(mk_out_scope argsno) t pattern
 *
 *   ? args = t
 *
 *   where argsn = length args and the pattern matches t
 *
 *  found is called on every selected term to map them
 *  postprocess is called on the entire term after selection
 *)
let select_term 
  low_status ~found ~postprocess (context,term) (wanted,path) 
=
  let is_found status ctx t wanted =
    (* we could lift wanted step-by-step *)
    pp(lazy("is_found: "^ppterm status (ctx,t)));
    try true, unify status ctx (ctx, t) wanted
    with 
    | Error (_, Some (NCicUnification.UnificationFailure _))
    | Error (_, Some (NCicUnification.Uncertain _)) -> false, status
  in
  let match_term status ctx (wanted : cic_term) t =
    let rec aux ctx (status,already_found) t =
      let b, status = is_found status ctx t wanted in
      if b then
         let status , (_,t) = found status (ctx, t) in 
         (status,true),t
      else
        let _,_,_,subst,_ = status#obj in
        match t with
        | NCic.Meta (i,lc) when List.mem_assoc i subst ->
            let _,_,t,_ = NCicUtils.lookup_subst i subst in
            aux ctx (status,already_found) t
        | NCic.Meta _ -> (status,already_found),t
        | _ ->
          NCicUntrusted.map_term_fold_a status (fun e c -> e::c) ctx aux
           (status,already_found) t
     in 
       aux ctx (status,false) t
  in 
  let _,_,_,subst,_ = low_status#obj in
  let rec select status ctx pat cic = 
    match pat, cic with
    | _, NCic.Meta (i,lc) when List.mem_assoc i subst ->
        let cic = 
          let _,_,t,_ = NCicUtils.lookup_subst i subst in
          NCicSubstitution.subst_meta status lc t
        in
        select status ctx pat cic
    | NCic.LetIn (_,t1,s1,b1), NCic.LetIn (n,t2,s2,b2) ->
        let status, t = select status ctx t1 t2 in
        let status, s = select status ctx s1 s2 in
        let ctx = (n, NCic.Def (s2,t2)) :: ctx in
        let status, b = select status ctx b1 b2 in
        status, NCic.LetIn (n,t,s,b)
    | NCic.Lambda (_,s1,t1), NCic.Lambda (n,s2,t2) ->
        let status, s = select status ctx s1 s2 in
        let ctx = (n, NCic.Decl s2) :: ctx in
        let status, t = select status ctx t1 t2 in
        status, NCic.Lambda (n,s,t)
    | NCic.Prod (_,s1,t1), NCic.Prod (n,s2,t2) ->
        let status, s = select status ctx s1 s2 in
        let ctx = (n, NCic.Decl s2) :: ctx in
        let status, t = select status ctx t1 t2 in
        status, NCic.Prod (n,s,t)
    | NCic.Appl l1, NCic.Appl l2 when List.length l1 = List.length l2 ->
        let status, l = 
           List.fold_left2
             (fun (status,l) x y -> 
              let status, x = select status ctx x y in
              status, x::l)
             (status,[]) l1 l2
        in
        status, NCic.Appl (List.rev l)
    | NCic.Match (_,ot1,t1,pl1), NCic.Match (u,ot2,t2,pl2)
      when List.length pl1 = List.length pl2 ->
        let status, t = select status ctx t1 t2 in
        let status, ot = select status ctx ot1 ot2 in
        let status, pl = 
           List.fold_left2
             (fun (status,l) x y -> 
              let status, x = select status ctx x y in
              status, x::l)
             (status,[]) pl1 pl2
        in
        status, NCic.Match (u,ot,t,List.rev pl)
    | NCic.Implicit `Hole, t -> 
        (match wanted with
        | Some wanted -> 
             let status', wanted = disambiguate status ctx wanted `XTNone in
             pp(lazy("wanted: "^ppterm status' wanted));
             let (status',found), t' = match_term status' ctx wanted t in
              if found then status',t' else status,t
        | None ->
           let (status,_),t = match_term status ctx (ctx,t) t in
            status,t)
    | NCic.Implicit _, t -> status, t
    | _,t -> 
        fail (lazy ("malformed pattern: " ^ status#ppterm ~metasenv:[]
          ~context:[] ~subst:[] pat ^ " against " ^ 
          status#ppterm ~metasenv:[] ~subst:[] ~context:[] t))
  in
  pp(lazy ("select in: "^ppterm low_status (context,term)));
  let status, term = select low_status context path term in
  let term = (context, term) in
  pp(lazy ("postprocess: "^ppterm low_status term));
  postprocess status term
;;

let analyse_indty status ty = 
 let status, reduct = whd status (ctx_of ty) ty in
 let ref, args =
  match reduct with
   | _,NCic.Const ref -> ref, []
   | _,NCic.Appl (NCic.Const (NRef.Ref (_,(NRef.Ind _)) as ref) :: args) -> 
         ref, args
   | _,_ -> fail (lazy ("not an inductive type: " ^ ppterm status ty)) in
 let _,lno,tl,_,i = NCicEnvironment.get_checked_indtys status ref in
 let _,_,_,cl = List.nth tl i in
 let consno = List.length cl in
 let left, right = HExtlib.split_nth lno args in
 status, (ref, consno, left, right)
;;

let apply_subst status ctx t =
 let status, (_,t) = relocate status ctx t in
 let _,_,_,subst,_ = status#obj in
  status, (ctx, NCicUntrusted.apply_subst status subst ctx t)
;;

let apply_subst_context status ~fix_projections ctx =
 let _,_,_,subst,_ = status#obj in
  NCicUntrusted.apply_subst_context status ~fix_projections subst ctx
;;

let metas_of_term status (context,t) =
 let _,_,_,subst,_ = status#obj in
 NCicUntrusted.metas_of_term status subst context t
;;

(* ============= move this elsewhere ====================*)

class type ['stack] g_status =
 object
  inherit g_pstatus
  method stack: 'stack
 end

class virtual ['stack] status =
 fun (o: NCic.obj) (s: 'stack) ->
 object (self)
   inherit (pstatus o)
   val stack = s
   method stack = stack
   method set_stack s = {< stack = s >}
   method set_status : 'status. 'stack #g_status as 'status -> 'self
   = fun o -> (self#set_pstatus o)#set_stack o#stack
  end

class type virtual lowtac_status = [unit] status

type 'status lowtactic = #lowtac_status as 'status -> int -> 'status

class type virtual tac_status = [Continuationals.Stack.t] status

type 'status tactic = #tac_status as 'status -> 'status

let pp_tac_status (status: #tac_status) = 
  prerr_endline (status#ppobj status#obj);
  prerr_endline ("STACK:\n" ^ Continuationals.Stack.pp status#stack)
;;

module NCicInverseRelIndexable : Discrimination_tree.Indexable
with type input = cic_term and type constant_name = NUri.uri = struct

open Discrimination_tree

type input = cic_term
type constant_name = NUri.uri

let ppelem = function
  | Constant (uri,arity) -> 
      "("^NUri.name_of_uri uri ^ "," ^ string_of_int arity^")"
  | Bound (i,arity) -> 
      "("^string_of_int i ^ "," ^ string_of_int arity^")"
  | Variable -> "?"
  | Proposition -> "Prop"
  | Datatype -> "Type"
  | Dead -> "Dead"
;;

let string_of_path l = String.concat "." (List.map ppelem l) ;;

let path_string_of (ctx,t) =
  let len_ctx = List.length ctx in
  let rec aux arity = function
    | NCic.Appl ((NCic.Meta _|NCic.Implicit _)::_) -> [Variable]
    | NCic.Appl (NCic.Lambda _ :: _) -> [Variable] (* maybe we should b-reduce *)
    | NCic.Appl [] -> assert false
    | NCic.Appl (hd::tl) ->
        aux (List.length tl) hd @ List.flatten (List.map (aux 0) tl) 
    | NCic.Lambda _ | NCic.Prod _ -> [Variable]
        (* I think we should CicSubstitution.subst Implicit t *)
    | NCic.LetIn _ -> [Variable] (* z-reduce? *)
    | NCic.Meta _ | NCic.Implicit _ -> assert (arity = 0); [Variable]
    | NCic.Rel i -> [Bound (len_ctx - i, arity)]
    | NCic.Sort (NCic.Prop) -> assert (arity=0); [Proposition]
    | NCic.Sort _ -> assert (arity=0); [Datatype]
    | NCic.Const (NReference.Ref (u,_)) -> [Constant (u, arity)]
    | NCic.Match _ -> [Dead]
  in 
  let path = aux 0 t in
(*   prerr_endline (string_of_path path); *)
  path
;;

let compare e1 e2 =
  match e1,e2 with
  | Constant (u1,a1),Constant (u2,a2) -> 
       let x = NUri.compare u1 u2 in
       if x = 0 then Pervasives.compare a1 a2 else x
  | e1,e2 -> Pervasives.compare e1 e2
;;


end

module Ncic_termOT : Set.OrderedType with type t = cic_term =
 struct
   type t = cic_term
   let compare = Pervasives.compare
 end

module Ncic_termSet : Set.S with type elt = cic_term = Set.Make(Ncic_termOT)

module InvRelDiscriminationTree = 
   Discrimination_tree.Make(NCicInverseRelIndexable)(Ncic_termSet)

