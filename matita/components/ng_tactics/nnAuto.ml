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

open Printf

let print ?(depth=0) s = 
  prerr_endline (String.make (2*depth) ' '^Lazy.force s) 
let noprint ?(depth=0) _ = () 
let debug_print = noprint

open Continuationals.Stack
open NTacStatus
module Ast = NotationPt

(* ======================= statistics  ========================= *)

let app_counter = ref 0

module RHT = struct
  type t = NReference.reference
  let equal = NReference.eq
  let compare = NReference.compare
  let hash = NReference.hash
end;;

module RefHash = Hashtbl.Make(RHT);;

type info = {
  nominations : int ref;
  uses: int ref;
}

let statistics: info RefHash.t = RefHash.create 503

let incr_nominations tbl item =
  try
    let v = RefHash.find tbl item in incr v.nominations
  with Not_found ->
    RefHash.add tbl item {nominations = ref 1; uses = ref 0}

let incr_uses tbl item =
  try
    let v = RefHash.find tbl item in incr v.uses
  with Not_found -> assert false

let toref f tbl t =
  match t with
    | Ast.NRef n -> 
	f tbl n
    | Ast.NCic _  (* local candidate *)
    | _  ->  ()

let is_relevant tbl item =
  try
    let v = RefHash.find tbl item in
      if !(v.nominations) < 60 then true (* not enough info *)
      else if !(v.uses) = 0 then false
      else true
  with Not_found -> true

let print_stat status tbl =
  let l = RefHash.fold (fun a v l -> (a,v)::l) tbl [] in
  let relevance v = float !(v.uses) /. float !(v.nominations) in
  let vcompare (_,v1) (_,v2) =
    Pervasives.compare (relevance v1) (relevance v2) in
  let l = List.sort vcompare l in
  let short_name r = 
    Filename.chop_extension 
      (Filename.basename (NReference.string_of_reference r))
  in
  let vstring (a,v)=
      short_name a ^ ": rel = " ^
      (string_of_float (relevance v)) ^
      "; uses = " ^ (string_of_int !(v.uses)) ^
      "; nom = " ^ (string_of_int !(v.nominations)) in
  lazy ("\n\nSTATISTICS:\n" ^
	  String.concat "\n" (List.map vstring l)) 

(* ======================= utility functions ========================= *)
module IntSet = Set.Make(struct type t = int let compare = compare end)

let get_sgoalty status g =
 let _,_,metasenv,subst,_ = status#obj in
 try
   let _, ctx, ty = NCicUtils.lookup_meta g metasenv in
   let ty = NCicUntrusted.apply_subst status subst ctx ty in
   let ctx = NCicUntrusted.apply_subst_context status
     ~fix_projections:true subst ctx
   in
     NTacStatus.mk_cic_term ctx ty
 with NCicUtils.Meta_not_found _ as exn -> fail ~exn (lazy "get_sgoalty")
;;

let deps status g =
  let gty = get_sgoalty status g in
  metas_of_term status gty
;;

let menv_closure status gl = 
  let rec closure acc = function
    | [] -> acc
    | x::l when IntSet.mem x acc -> closure acc l
    | x::l -> closure (IntSet.add x acc) (deps status x @ l)
  in closure IntSet.empty gl
;;

(* we call a "fact" an object whose hypothesis occur in the goal 
   or in types of goal-variables *)
let branch status ty =  
  let status, ty, metas = saturate ~delta:0 status ty in
  noprint (lazy ("saturated ty :" ^ (ppterm status ty)));
  let g_metas = metas_of_term status ty in
  let clos = menv_closure status g_metas in
  (* let _,_,metasenv,_,_ = status#obj in *)
  let menv = 
    List.fold_left
      (fun acc m ->
         let _, m = term_of_cic_term status m (ctx_of m) in
         match m with 
         | NCic.Meta(i,_) -> IntSet.add i acc
         | _ -> assert false)
      IntSet.empty metas
  in 
  (* IntSet.subset menv clos *)
  IntSet.cardinal(IntSet.diff menv clos)

let is_a_fact status ty = branch status ty = 0

let is_a_fact_obj s uri = 
  let obj = NCicEnvironment.get_checked_obj s uri in
  match obj with
    | (_,_,[],[],NCic.Constant(_,_,_,ty,_)) ->
        is_a_fact s (mk_cic_term [] ty)
(* aggiungere i costruttori *)
    | _ -> false

let is_a_fact_ast status subst metasenv ctx cand = 
 noprint ~depth:0 
   (lazy ("checking facts " ^ NotationPp.pp_term status cand)); 
 let status, t = disambiguate status ctx ("",0,cand) `XTNone in
 let status,t = term_of_cic_term status t ctx in
 let ty = NCicTypeChecker.typeof status subst metasenv ctx t in
   is_a_fact status (mk_cic_term ctx ty)

let current_goal status = 
  let open_goals = head_goals status#stack in
  assert (List.length open_goals  = 1);
  let open_goal = List.hd open_goals in
  let gty = get_goalty status open_goal in
  let ctx = ctx_of gty in
    open_goal, ctx, gty

let height_of_ref status (NReference.Ref (uri, x)) = 
  match x with
  | NReference.Decl 
  | NReference.Ind _ 
  | NReference.Con _
  | NReference.CoFix _ -> 
      let _,height,_,_,_ = NCicEnvironment.get_checked_obj status uri in
      height 
  | NReference.Def h -> h 
  | NReference.Fix (_,_,h) -> h 
;;

(*************************** height functions ********************************)
let fast_height_of_term status t =
 let h = ref 0 in
 let rec aux =
  function
     NCic.Meta (_,(_,NCic.Ctx l)) -> List.iter aux l
   | NCic.Meta _ -> ()
   | NCic.Rel _
   | NCic.Sort _ -> ()
   | NCic.Implicit _ -> assert false
   | NCic.Const nref -> 
(*
                   prerr_endline (status#ppterm ~metasenv:[] ~subst:[]
                   ~context:[] t ^ ":" ^ string_of_int (height_of_ref status nref));            
*)
       h := max !h (height_of_ref status nref)
   | NCic.Prod (_,t1,t2)
   | NCic.Lambda (_,t1,t2) -> aux t1; aux t2
   | NCic.LetIn (_,s,ty,t) -> aux s; aux ty; aux t
   | NCic.Appl l -> List.iter aux l
   | NCic.Match (_,outty,t,pl) -> aux outty; aux t; List.iter aux pl
 in
  aux t; !h
;;

let height_of_goal g status = 
  let ty = get_goalty status g in
  let context = ctx_of ty in
  let _, ty = term_of_cic_term status ty (ctx_of ty) in
  let h = ref (fast_height_of_term status ty) in
  List.iter 
    (function 
       | _, NCic.Decl ty -> h := max !h (fast_height_of_term status ty)
       | _, NCic.Def (bo,ty) -> 
           h := max !h (fast_height_of_term status ty);
           h := max !h (fast_height_of_term status bo);
    )
    context;
  !h
;;      

let height_of_goals status = 
  let open_goals = head_goals status#stack in
  assert (List.length open_goals > 0);
  let h = ref 1 in
  List.iter 
    (fun open_goal ->
       h := max !h (height_of_goal open_goal status))
     open_goals;
  noprint (lazy ("altezza sequente: " ^ string_of_int !h));
  !h
;;

(* =============================== paramod =========================== *)
let solve f status eq_cache goal =
(*
  let f = 
    if fast then NCicParamod.fast_eq_check
    else NCicParamod.paramod in
*)
  let n,h,metasenv,subst,o = status#obj in
  let gname, ctx, gty = List.assoc goal metasenv in
  let gty = NCicUntrusted.apply_subst status subst ctx gty in
  let build_status (pt, _, metasenv, subst) =
    try
      debug_print (lazy ("refining: "^(status#ppterm ctx subst metasenv pt)));
      let stamp = Unix.gettimeofday () in 
      let metasenv, subst, pt, pty =
	(* NCicRefiner.typeof status
          (* (status#set_coerc_db NCicCoercion.empty_db) *)
          metasenv subst ctx pt None in
          debug_print (lazy ("refined: "^(status#ppterm ctx subst metasenv pt)));
          noprint (lazy ("synt: "^(status#ppterm ctx subst metasenv pty)));
          let metasenv, subst =
            NCicUnification.unify status metasenv subst ctx gty pty *)
        NCicRefiner.typeof 
          (status#set_coerc_db NCicCoercion.empty_db) 
          metasenv subst ctx pt (`XTSome gty) 
        in 
          noprint (lazy (Printf.sprintf "Refined in %fs"
                     (Unix.gettimeofday() -. stamp))); 
          let status = status#set_obj (n,h,metasenv,subst,o) in
          let metasenv = List.filter (fun j,_ -> j <> goal) metasenv in
          let subst = (goal,(gname,ctx,pt,pty)) :: subst in
            Some (status#set_obj (n,h,metasenv,subst,o))
    with 
        NCicRefiner.RefineFailure msg 
      | NCicRefiner.Uncertain msg ->
          debug_print (lazy ("WARNING U: refining in fast_eq_check failed\n" ^
                        snd (Lazy.force msg) ^	
			"\n in the environment\n" ^ 
			status#ppmetasenv subst metasenv)); None
      | NCicRefiner.AssertFailure msg -> 
          debug_print (lazy ("WARNING F: refining in fast_eq_check failed" ^
                        Lazy.force msg ^
			"\n in the environment\n" ^ 
			status#ppmetasenv subst metasenv)); None
      | Sys.Break as e -> raise e
      | _ -> None
    in
    HExtlib.filter_map build_status
      (f status metasenv subst ctx eq_cache (NCic.Rel ~-1,gty))
;;

let fast_eq_check eq_cache status (goal:int) =
  match solve NCicParamod.fast_eq_check status eq_cache goal with
  | [] -> raise (Error (lazy "no proof found",None))
  | s::_ -> s
;;

let dist_fast_eq_check eq_cache s = 
  NTactics.distribute_tac (fast_eq_check eq_cache) s
;;

let auto_eq_check eq_cache status =
  try 
    let s = dist_fast_eq_check eq_cache status in
      [s]
  with
    | Error _ -> debug_print (lazy ("no paramod proof found"));[]
;;

let index_local_equations eq_cache status =
  noprint (lazy "indexing equations");
  let open_goals = head_goals status#stack in
  let open_goal = List.hd open_goals in
  let ngty = get_goalty status open_goal in
  let _,_,metasenv,subst,_ = status#obj in
  let ctx = apply_subst_context ~fix_projections:true status (ctx_of ngty) in
  let c = ref 0 in
  List.fold_left 
    (fun eq_cache _ ->
       c:= !c+1;
       let t = NCic.Rel !c in
         try
           let ty = NCicTypeChecker.typeof status subst metasenv ctx t in
           if is_a_fact status (mk_cic_term ctx ty) then
             (debug_print(lazy("eq indexing " ^ (status#ppterm ctx subst metasenv ty)));
              NCicParamod.forward_infer_step status metasenv subst ctx eq_cache t ty)
           else 
             (noprint (lazy ("not a fact: " ^ (status#ppterm ctx subst metasenv ty)));
              eq_cache)
         with 
           | NCicTypeChecker.TypeCheckerFailure _
           | NCicTypeChecker.AssertFailure _ -> eq_cache) 
    eq_cache ctx
;;

let index_local_equations2 eq_cache status open_goal lemmas nohyps =
  noprint (lazy "indexing equations");
  let eq_cache,lemmas =
   match lemmas with
      None -> eq_cache,[]
    | Some l -> NCicParamod.empty_state,l
  in
  let ngty = get_goalty status open_goal in
  let _,_,metasenv,subst,_ = status#obj in
  let ctx = apply_subst_context ~fix_projections:true status (ctx_of ngty) in
  let status,lemmas =
   List.fold_left
    (fun (status,lemmas) l ->
      let status,l = NTacStatus.disambiguate status ctx l `XTNone in
      let status,l = NTacStatus.term_of_cic_term status l ctx in
       status,l::lemmas)
    (status,[]) lemmas in
  let local_equations =
   if nohyps then [] else
    List.map (fun i -> NCic.Rel (i + 1))
     (HExtlib.list_seq 1 (List.length ctx)) in
  let lemmas = lemmas @ local_equations in
  List.fold_left 
    (fun eq_cache t ->
         try
           let ty = NCicTypeChecker.typeof status subst metasenv ctx t in
           if is_a_fact status (mk_cic_term ctx ty) then
             (debug_print(lazy("eq indexing " ^ (status#ppterm ctx subst metasenv ty)));
              NCicParamod.forward_infer_step status metasenv subst ctx eq_cache t ty)
           else 
             (noprint (lazy ("not a fact: " ^ (status#ppterm ctx subst metasenv ty)));
              eq_cache)
         with 
           | NCicTypeChecker.TypeCheckerFailure _
           | NCicTypeChecker.AssertFailure _ -> eq_cache)
    eq_cache lemmas
;;

let fast_eq_check_tac ~params s = 
  let unit_eq = index_local_equations s#eq_cache s in   
  dist_fast_eq_check unit_eq s
;;

let paramod eq_cache status goal =
  match solve NCicParamod.paramod status eq_cache goal with
  | [] -> raise (Error (lazy "no proof found",None))
  | s::_ -> s
;;

let paramod_tac ~params s = 
  let unit_eq = index_local_equations s#eq_cache s in   
  NTactics.distribute_tac (paramod unit_eq) s
;;

let demod eq_cache status goal =
  match solve NCicParamod.demod status eq_cache goal with
  | [] -> raise (Error (lazy "no progress",None))
  | s::_ -> s
;;

let demod_tac ~params s = 
  let unit_eq s i =
   index_local_equations2 s#eq_cache s i (fst params)
    (List.mem_assoc "nohyps" (snd params))
  in   
   NTactics.distribute_tac (fun s i -> demod (unit_eq s i) s i) s
;;

(*
let fast_eq_check_tac_all  ~params eq_cache status = 
  let g,_,_ = current_goal status in
  let allstates = fast_eq_check_all status eq_cache g in
  let pseudo_low_tac s _ _ = s in
  let pseudo_low_tactics = 
    List.map pseudo_low_tac allstates 
  in
    List.map (fun f -> NTactics.distribute_tac f status) pseudo_low_tactics
;;
*)

(*
let demod status eq_cache goal =
  let n,h,metasenv,subst,o = status#obj in
  let gname, ctx, gty = List.assoc goal metasenv in
  let gty = NCicUntrusted.apply_subst subst ctx gty in

let demod_tac ~params s = 
  let unit_eq = index_local_equations s#eq_cache s in   
  dist_fast_eq_check unit_eq s
*)

(*************** subsumption ****************)

let close_wrt_context status =
  List.fold_left 
    (fun ty ctx_entry -> 
        match ctx_entry with 
       | name, NCic.Decl t -> NCic.Prod(name,t,ty)
       | name, NCic.Def(bo, _) -> NCicSubstitution.subst status bo ty)
;;

let args_for_context ?(k=1) ctx =
  let _,args =
    List.fold_left 
      (fun (n,l) ctx_entry -> 
         match ctx_entry with 
           | name, NCic.Decl t -> n+1,NCic.Rel(n)::l
           | name, NCic.Def(bo, _) -> n+1,l)
      (k,[]) ctx in
    args

let constant_for_meta status ctx ty i =
  let name = "cic:/foo"^(string_of_int i)^".con" in
  let uri = NUri.uri_of_string name in
  let ty = close_wrt_context status ty ctx in
  (* prerr_endline (status#ppterm [] [] [] ty); *)
  let attr = (`Generated,`Definition,`Local) in
  let obj = NCic.Constant([],name,None,ty,attr) in
    (* Constant  of relevance * string * term option * term * c_attr *)
    (uri,0,[],[],obj)

(* not used *)
let refresh metasenv =
  List.fold_left 
    (fun (metasenv,subst) (i,(iattr,ctx,ty)) ->
       let ikind = NCicUntrusted.kind_of_meta iattr in
       let metasenv,j,instance,ty = 
         NCicMetaSubst.mk_meta ~attrs:iattr 
           metasenv ctx ~with_type:ty ikind in
       let s_entry = i,(iattr, ctx, instance, ty) in
       let metasenv = List.filter (fun x,_ -> i <> x) metasenv in
         metasenv,s_entry::subst) 
      (metasenv,[]) metasenv

(* close metasenv returns a ground instance of all the metas in the
metasenv, insantiatied with axioms, and the list of these axioms *)
let close_metasenv status metasenv subst = 
  (*
  let metasenv = NCicUntrusted.apply_subst_metasenv subst metasenv in
  *)
  let metasenv = NCicUntrusted.sort_metasenv status subst metasenv in 
    List.fold_left 
      (fun (subst,objs) (i,(iattr,ctx,ty)) ->
         let ty = NCicUntrusted.apply_subst status subst ctx ty in
         let ctx = 
           NCicUntrusted.apply_subst_context status ~fix_projections:true 
             subst ctx in
         let (uri,_,_,_,obj) as okind = 
           constant_for_meta status ctx ty i in
         try
           NCicEnvironment.check_and_add_obj status okind;
           let iref = NReference.reference_of_spec uri NReference.Decl in
           let iterm =
             let args = args_for_context ctx in
               if args = [] then NCic.Const iref 
               else NCic.Appl(NCic.Const iref::args)
           in
           (* prerr_endline (status#ppterm ctx [] [] iterm); *)
           let s_entry = i, ([], ctx, iterm, ty)
           in s_entry::subst,okind::objs
         with
            Sys.Break as e -> raise e
          | _ -> assert false)
      (subst,[]) metasenv
;;

let ground_instances status gl =
  let _,_,metasenv,subst,_ = status#obj in
  let subset = menv_closure status gl in
  let submenv = List.filter (fun (x,_) -> IntSet.mem x subset) metasenv in
(*
  let submenv = metasenv in
*)
  let subst, objs = close_metasenv status submenv subst in
  try
    List.iter
      (fun i -> 
         let (_, ctx, t, _) = List.assoc i subst in
           noprint (lazy (status#ppterm ctx [] [] t));
           List.iter 
             (fun (uri,_,_,_,_) as obj -> 
                NCicEnvironment.invalidate_item (`Obj (uri, obj))) 
             objs;
           ())
      gl
  with
      Not_found -> assert false 
  (* (ctx,t) *)
;;

let replace_meta status i args target = 
  let rec aux k = function
    (* TODO: local context *)
    | NCic.Meta (j,lc) when i = j ->
        (match args with
           | [] -> NCic.Rel 1
           | _ -> let args = 
               List.map (NCicSubstitution.subst_meta status lc) args in
               NCic.Appl(NCic.Rel k::args))
    | NCic.Meta (j,lc) as m ->
        (match lc with
           _,NCic.Irl _ -> m
         | n,NCic.Ctx l ->
            NCic.Meta
             (i,(0,NCic.Ctx
                 (List.map (fun t ->
                   aux k (NCicSubstitution.lift status n t)) l))))
    | t -> NCicUtils.map status (fun _ k -> k+1) k aux t
 in
   aux 1 target
;;

let close_wrt_metasenv status subst =
  List.fold_left 
    (fun ty (i,(iattr,ctx,mty)) ->
       let mty = NCicUntrusted.apply_subst status subst ctx mty in
       let ctx = 
         NCicUntrusted.apply_subst_context status ~fix_projections:true 
           subst ctx in
       let cty = close_wrt_context status mty ctx in
       let name = "foo"^(string_of_int i) in
       let ty = NCicSubstitution.lift status 1 ty in
       let args = args_for_context ~k:1 ctx in
         (* prerr_endline (status#ppterm ctx [] [] iterm); *)
       let ty = replace_meta status i args ty
       in
       NCic.Prod(name,cty,ty))
;;

let close status g =
  let _,_,metasenv,subst,_ = status#obj in
  let subset = menv_closure status [g] in
  let subset = IntSet.remove g subset in
  let elems = IntSet.elements subset in 
  let _, ctx, ty = NCicUtils.lookup_meta g metasenv in
  let ty = NCicUntrusted.apply_subst status subst ctx ty in
  noprint (lazy ("metas in " ^ (status#ppterm ctx [] metasenv ty)));
  noprint (lazy (String.concat ", " (List.map string_of_int elems)));
  let submenv = List.filter (fun (x,_) -> IntSet.mem x subset) metasenv in
  let submenv = List.rev (NCicUntrusted.sort_metasenv status subst submenv) in 
(*  
    let submenv = metasenv in
*)
  let ty = close_wrt_metasenv status subst ty submenv in
    noprint (lazy (status#ppterm ctx [] [] ty));
    ctx,ty
;;

(****************** smart application ********************)

let saturate_to_ref status metasenv subst ctx nref ty =
  let height = height_of_ref status nref in
  let rec aux metasenv ty args = 
    let ty,metasenv,moreargs =  
      NCicMetaSubst.saturate status ~delta:height metasenv subst ctx ty 0 in 
    match ty with
      | NCic.Const(NReference.Ref (_,NReference.Def _) as nre) 
	  when nre<>nref ->
	  let _, _, bo, _, _, _ = NCicEnvironment.get_checked_def status nre in 
	    aux metasenv bo (args@moreargs)
      | NCic.Appl(NCic.Const(NReference.Ref (_,NReference.Def _) as nre)::tl) 
	  when nre<>nref ->
	  let _, _, bo, _, _, _ = NCicEnvironment.get_checked_def status nre in
	    aux metasenv (NCic.Appl(bo::tl)) (args@moreargs) 
    | _ -> ty,metasenv,(args@moreargs)
  in
    aux metasenv ty []

let smart_apply t unit_eq status g = 
  let n,h,metasenv,subst,o = status#obj in
  let gname, ctx, gty = List.assoc g metasenv in
  (* let ggty = mk_cic_term context gty in *)
  let status, t = disambiguate status ctx t `XTNone in
  let status,t = term_of_cic_term status t ctx in
  let _,_,metasenv,subst,_ = status#obj in
  let ty = NCicTypeChecker.typeof status subst metasenv ctx t in
  let ty,metasenv,args = 
    match gty with
      | NCic.Const(nref)
      | NCic.Appl(NCic.Const(nref)::_) -> 
	  saturate_to_ref status metasenv subst ctx nref ty
      | _ -> 
	  NCicMetaSubst.saturate status metasenv subst ctx ty 0 in
  let metasenv,j,inst,_ = NCicMetaSubst.mk_meta metasenv ctx `IsTerm in
  let status = status#set_obj (n,h,metasenv,subst,o) in
  let pterm = if args=[] then t else 
    match t with
      | NCic.Appl l -> NCic.Appl(l@args) 
      | _ -> NCic.Appl(t::args) 
  in
  noprint(lazy("pterm " ^ (status#ppterm ctx [] [] pterm)));
  noprint(lazy("pty " ^ (status#ppterm ctx [] [] ty)));
  let eq_coerc =       
    let uri = 
      NUri.uri_of_string "cic:/matita/basics/logic/eq_coerc.con" in
    let ref = NReference.reference_of_spec uri (NReference.Def(2)) in
      NCic.Const ref
  in
  let smart = 
    NCic.Appl[eq_coerc;ty;NCic.Implicit `Type;pterm;inst] in
  let smart = mk_cic_term ctx smart in 
    try
      let status = instantiate status g smart in
      let _,_,metasenv,subst,_ = status#obj in
      let _,ctx,jty = List.assoc j metasenv in
      let jty = NCicUntrusted.apply_subst status subst ctx jty in
        debug_print(lazy("goal " ^ (status#ppterm ctx [] [] jty)));
        let res = fast_eq_check unit_eq status j in
        debug_print(lazy("ritorno da fast_eq_check"));
        res
    with
      | NCicEnvironment.ObjectNotFound s as e ->
          raise (Error (lazy "eq_coerc non yet defined",Some e))
      | Error _ as e -> debug_print (lazy "error"); raise e
(* FG: for now we catch TypeCheckerFailure; to be understood *)  
      | NCicTypeChecker.TypeCheckerFailure _ ->
          debug_print (lazy "TypeCheckerFailure");
          raise (Error (lazy "no proof found",None))
;;

let compare_statuses ~past ~present =
 let _,_,past,_,_ = past#obj in 
 let _,_,present,_,_ = present#obj in 
 List.map fst (List.filter (fun (i,_) -> not(List.mem_assoc i past)) present),
 List.map fst (List.filter (fun (i,_) -> not (List.mem_assoc i present)) past)
;;

(* paramodulation has only an implicit knoweledge of the symmetry of equality;
   hence it is in trouble in proving (a = b) = (b = a) *) 
let try_sym tac status g =
  let sym_eq = Ast.Appl [Ast.Ident("sym_eq",None); Ast.Implicit `Vector] in
  let _,_,metasenv,subst,_ = status#obj in
  let _, context, gty = List.assoc g metasenv in
  let is_eq = 
    NCicParamod.is_equation status metasenv subst context gty 
  in
  if is_eq then
    try tac status g
    with Error _ ->
      let new_status = instantiate_with_ast status g ("",0,sym_eq) in 
      let go, _ = compare_statuses ~past:status ~present:new_status in
      assert (List.length go  = 1);
      let ng = List.hd go in
      tac new_status ng
   else tac status g
;;

let smart_apply_tac t s =
  let unit_eq = index_local_equations s#eq_cache s in   
  NTactics.distribute_tac (try_sym (smart_apply t unit_eq)) s 
  (* NTactics.distribute_tac (smart_apply t unit_eq) s *)

let smart_apply_auto t eq_cache =
  NTactics.distribute_tac (try_sym (smart_apply t eq_cache)) 
  (* NTactics.distribute_tac (smart_apply t eq_cache) *)


(****************** types **************)


type th_cache = (NCic.context * InvRelDiscriminationTree.t) list

(* cartesian: term set list -> term list set *)
let rec cartesian =
 function
    [] -> NDiscriminationTree.TermListSet.empty
  | [l] ->
     NDiscriminationTree.TermSet.fold
      (fun x acc -> NDiscriminationTree.TermListSet.add [x] acc) l NDiscriminationTree.TermListSet.empty
  | he::tl ->
     let rest = cartesian tl in
      NDiscriminationTree.TermSet.fold
       (fun x acc ->
         NDiscriminationTree.TermListSet.fold (fun l acc' -> NDiscriminationTree.TermListSet.add (x::l) acc') rest acc
       ) he NDiscriminationTree.TermListSet.empty
;;

(* all_keys_of_cic_type: term -> term set *)
let all_keys_of_cic_type status metasenv subst context ty =
 let saturate ty =
  (* Here we are dropping the metasenv, but this should not raise any
     exception (hopefully...) *)
  let ty,_,hyps =
   NCicMetaSubst.saturate status ~delta:max_int metasenv subst context ty 0
  in
   ty,List.length hyps
 in
 let rec aux ty =
  match ty with
     NCic.Appl (he::tl) ->
      let tl' =
       List.map (fun ty ->
        let wty = NCicReduction.whd status ~delta:0 ~subst context ty in
         if ty = wty then
          NDiscriminationTree.TermSet.add ty (aux ty)
         else
          NDiscriminationTree.TermSet.union
           (NDiscriminationTree.TermSet.add  ty (aux  ty))
           (NDiscriminationTree.TermSet.add wty (aux wty))
        ) tl
      in
       NDiscriminationTree.TermListSet.fold
        (fun l acc -> NDiscriminationTree.TermSet.add (NCic.Appl l) acc)
        (cartesian ((NDiscriminationTree.TermSet.singleton he)::tl'))
        NDiscriminationTree.TermSet.empty
   | _ -> NDiscriminationTree.TermSet.empty
 in
  let ty,ity = saturate ty in
  let wty,iwty = saturate (NCicReduction.whd status ~delta:0 ~subst context ty) in
   if ty = wty then
    [ity, NDiscriminationTree.TermSet.add ty (aux ty)]
   else
    [ity,  NDiscriminationTree.TermSet.add  ty (aux  ty) ;
     iwty, NDiscriminationTree.TermSet.add wty (aux wty) ]
;;

let all_keys_of_type status t =
 let _,_,metasenv,subst,_ = status#obj in
 let context = ctx_of t in
 let status, t = apply_subst status context t in
 let keys =
  all_keys_of_cic_type status metasenv subst context
   (snd (term_of_cic_term status t context))
 in
  status,
   List.map
    (fun (intros,keys) ->
      intros,
       NDiscriminationTree.TermSet.fold
        (fun t acc -> Ncic_termSet.add (mk_cic_term context t) acc)
        keys Ncic_termSet.empty
    ) keys
;;


let keys_of_type status orig_ty =
  (* Here we are dropping the metasenv (in the status), but this should not
     raise any exception (hopefully...) *)
  let _, ty, _ = saturate ~delta:max_int status orig_ty in
  let _, ty = apply_subst status (ctx_of ty) ty in
  let keys =
(*
    let orig_ty' = NCicTacReduction.normalize ~subst context orig_ty in
    if orig_ty' <> orig_ty then
     let ty',_,_= NCicMetaSubst.saturate ~delta:0 metasenv subst context orig_ty' 0 in
      [ty;ty']
    else
     [ty]
*)
   [ty] in
(*CSC: strange: we keep ty, ty normalized and ty ~delta:(h-1) *)
  let keys = 
    let _, ty = term_of_cic_term status ty (ctx_of ty) in
    match ty with
    | NCic.Const (NReference.Ref (_,(NReference.Def h | NReference.Fix (_,_,h)))) 
    | NCic.Appl (NCic.Const(NReference.Ref(_,(NReference.Def h | NReference.Fix (_,_,h))))::_) 
       when h > 0 ->
         let _,ty,_= saturate status ~delta:(h-1) orig_ty in
         ty::keys
    | _ -> keys
  in
  status, keys
;;

let all_keys_of_term status t =
 let status, orig_ty = typeof status (ctx_of t) t in
  all_keys_of_type status orig_ty
;;

let keys_of_term status t =
  let status, orig_ty = typeof status (ctx_of t) t in
    keys_of_type status orig_ty
;;

let mk_th_cache status gl = 
  List.fold_left 
    (fun (status, acc) g ->
       let gty = get_goalty status g in
       let ctx = ctx_of gty in
       noprint(lazy("th cache for: "^ppterm status gty));
       noprint(lazy("th cache in: "^ppcontext status ctx));
       if List.mem_assq ctx acc then status, acc else
         let idx = InvRelDiscriminationTree.empty in
         let status,_,idx = 
           List.fold_left 
             (fun (status, i, idx) _ -> 
                let t = mk_cic_term ctx (NCic.Rel i) in
                let status, keys = keys_of_term status t in
                noprint(lazy("indexing: "^ppterm status t ^ ": " ^ string_of_int (List.length keys)));
                let idx =
                  List.fold_left (fun idx k -> 
                    InvRelDiscriminationTree.index idx k t) idx keys
                in
                status, i+1, idx)
             (status, 1, idx) ctx
          in
         status, (ctx, idx) :: acc)
    (status,[]) gl
;;

let all_elements ctx cache =
  let dummy = mk_cic_term ctx (NCic.Meta (0,(0, (NCic.Irl 0)))) in
    try
      let idx = List.assq ctx cache in
      Ncic_termSet.elements 
        (InvRelDiscriminationTree.retrieve_unifiables idx dummy)
    with Not_found -> []

let add_to_th t c ty = 
  let key_c = ctx_of t in
  if not (List.mem_assq key_c c) then
      (key_c ,InvRelDiscriminationTree.index 
               InvRelDiscriminationTree.empty ty t ) :: c 
  else
    let rec replace = function
      | [] -> []
      | (x, idx) :: tl when x == key_c -> 
          (x, InvRelDiscriminationTree.index idx ty t) :: tl
      | x :: tl -> x :: replace tl
    in 
      replace c
;;

let rm_from_th t c ty = 
  let key_c = ctx_of t in
  if not (List.mem_assq key_c c) then assert false
  else
    let rec replace = function
      | [] -> []
      | (x, idx) :: tl when x == key_c -> 
          (x, InvRelDiscriminationTree.remove_index idx ty t) :: tl
      | x :: tl -> x :: replace tl
    in 
      replace c
;;

let pp_idx status idx =
   InvRelDiscriminationTree.iter idx
      (fun k set ->
         noprint(lazy("K: " ^ NCicInverseRelIndexable.string_of_path k));
         Ncic_termSet.iter 
           (fun t -> debug_print(lazy("\t"^ppterm status t))) 
           set)
;;

let pp_th (status: #NTacStatus.pstatus) = 
  List.iter 
    (fun ctx, idx ->
       noprint(lazy( "-----------------------------------------------"));
       noprint(lazy( (status#ppcontext ~metasenv:[] ~subst:[] ctx)));
       noprint(lazy( "||====>  "));
       pp_idx status idx)
;;

let search_in_th gty th = 
  let c = ctx_of gty in
  let rec aux acc = function
   | [] -> (* Ncic_termSet.elements *) acc
   | (_::tl) as k ->
       try 
         let idx = List.assoc(*q*) k th in
         let acc = Ncic_termSet.union acc 
           (InvRelDiscriminationTree.retrieve_unifiables idx gty)
         in
         aux acc tl
       with Not_found -> aux acc tl
  in
    aux Ncic_termSet.empty c
;;

type flags = {
        do_types : bool; (* solve goals in Type *)
        last : bool; (* last goal: take first solution only  *)
        candidates: Ast.term list option;
        maxwidth : int;
        maxsize  : int;
        maxdepth : int;
        timeout  : float;
}

type cache =
    {facts : th_cache; (* positive results *)
     under_inspection : cic_term list * th_cache; (* to prune looping *)
     failures : th_cache; (* to avoid repetitions *)
     unit_eq : NCicParamod.state;
     trace: Ast.term list
    }

let add_to_trace status ~depth cache t =
  match t with
    | Ast.NRef _ -> 
	debug_print ~depth (lazy ("Adding to trace: " ^ NotationPp.pp_term status t));
	{cache with trace = t::cache.trace}
    | Ast.NCic _  (* local candidate *)
    | _  -> (*not an application *) cache 

let pptrace status tr = 
  (lazy ("Proof Trace: " ^ (String.concat ";" 
			      (List.map (NotationPp.pp_term status) tr))))
(* not used
let remove_from_trace cache t =
  match t with
    | Ast.NRef _ -> 
	(match cache.trace with 
	   |  _::tl -> {cache with trace = tl}
           | _ -> assert false)
    | Ast.NCic _  (* local candidate *)
    |  _  -> (*not an application *) cache *)

type sort = T | P
type goal = int * sort (* goal, depth, sort *)
type fail = goal * cic_term
type candidate = int * Ast.term (* unique candidate number, candidate *)

exception Gaveup of th_cache (* failure cache *)
exception Proved of NTacStatus.tac_status * Ast.term list

(* let close_failures _ c = c;; *)
(* let prunable _ _ _ = false;; *)
(* let cache_examine cache gty = `Notfound;; *)
(* let put_in_subst s _ _ _  = s;; *)
(* let add_to_cache_and_del_from_orlist_if_green_cut _ _ c _ _ o f _ = c, o, f, false ;; *)
(* let cache_add_underinspection c _ _ = c;; *)

let init_cache ?(facts=[]) ?(under_inspection=[],[])
    ?(failures=[])
    ?(unit_eq=NCicParamod.empty_state) 
    ?(trace=[]) 
    _ = 
    {facts = facts;
     failures = failures;
     under_inspection = under_inspection;
     unit_eq = unit_eq;
     trace = trace}

let only signature _context candidate = true
(*
        (* TASSI: nel trie ci mettiamo solo il body, non il ty *)
  let candidate_ty = 
   NCicTypeChecker.typeof ~subst:[] ~metasenv:[] [] candidate
  in
  let height = fast_height_of_term status candidate_ty in
  let rc = signature >= height in
  if rc = false then
    noprint (lazy ("Filtro: " ^ status#ppterm ~context:[] ~subst:[]
          ~metasenv:[] candidate ^ ": " ^ string_of_int height))
  else 
    noprint (lazy ("Tengo: " ^ status#ppterm ~context:[] ~subst:[]
          ~metasenv:[] candidate ^ ": " ^ string_of_int height));

  rc *)
;; 

let candidate_no = ref 0;;

let openg_no status = List.length (head_goals status#stack)

let sort_candidates status ctx candidates =
 let _,_,metasenv,subst,_ = status#obj in
  let branch cand =
    let status,ct = disambiguate status ctx ("",0,cand) `XTNone in
    let status,t = term_of_cic_term status ct ctx in
    let ty = NCicTypeChecker.typeof status subst metasenv ctx t in
    let res = branch status (mk_cic_term ctx ty) in
    noprint (lazy ("branch factor for: " ^ (ppterm status ct) ^ " = " 
		      ^ (string_of_int res)));
      res
  in 
  let candidates = List.map (fun t -> branch t,t) candidates in
  let candidates = 
     List.sort (fun (a,_) (b,_) -> a - b) candidates in 
  let candidates = List.map snd candidates in
    noprint (lazy ("candidates =\n" ^ (String.concat "\n" 
	(List.map (NotationPp.pp_term status) candidates))));
    candidates

let sort_new_elems l =
  List.sort (fun (_,s1) (_,s2) -> openg_no s1 - openg_no s2) l

let rec stack_goals level gs = 
  if level = 0 then []
  else match gs with 
    | [] -> assert false
    | (g,_,_,_)::s -> 
        let is_open = function
          | (_,Continuationals.Stack.Open i) -> Some i
          | (_,Continuationals.Stack.Closed _) -> None
        in
	  HExtlib.filter_map is_open g @ stack_goals (level-1) s
;;

let open_goals level status = stack_goals level status#stack
;;

let try_candidate ?(smart=0) flags depth status eq_cache ctx t =
  try
    let old_og_no = List.length (open_goals (depth+1) status) in
    debug_print ~depth (lazy ("try " ^ (string_of_int smart) ^ " : "
      ^ (NotationPp.pp_term status) t));
    let status = 
      if smart = 0 then NTactics.apply_tac ("",0,t) status
      else if smart = 1 then  
        smart_apply_auto ("",0,t) eq_cache status 
      else (* smart = 2: both *)
        try NTactics.apply_tac ("",0,t) status
        with Error _ -> 
          smart_apply_auto ("",0,t) eq_cache status 
    in
(* FG: this optimization rules out some applications of
 * lift_bind (from contribs/lambda_delta/Basic_2/substitution/lift.ma)
 *
    (* we compare the expected branching with the actual one and
       prune the candidate when the latter is larger. The optimization
       is meant to rule out stange applications of flexible terms,
       such as the application of eq_f that always succeeds.  
       There is some gain but less than expected *)
    let og_no = List.length (open_goals (depth+1) status) in
    let status, cict = disambiguate status ctx ("",0,t) None in
    let status,ct = term_of_cic_term status cict ctx in
    let _,_,metasenv,subst,_ = status#obj in
    let ty = NCicTypeChecker.typeof status subst metasenv ctx ct in
    let res = branch status (mk_cic_term ctx ty) in
    let diff = og_no - old_og_no in
    debug_print (lazy ("expected branching: " ^ (string_of_int res)));
    debug_print (lazy ("actual: branching" ^ (string_of_int diff))); 
    (* some flexibility *)
    if og_no - old_og_no > res then 
      (debug_print (lazy ("branch factor for: " ^ (ppterm status cict) ^ " = " 
		    ^ (string_of_int res) ^ " vs. " ^ (string_of_int og_no)));
       debug_print ~depth (lazy "strange application"); None)
    else 
*)      (incr candidate_no; Some ((!candidate_no,t),status))
   with Error (msg,exn) -> debug_print ~depth (lazy "failed"); None
;;

let sort_of status subst metasenv ctx t =
  let ty = NCicTypeChecker.typeof status subst metasenv ctx t in
  let metasenv',ty = NCicUnification.fix_sorts status metasenv subst ty in
   assert (metasenv = metasenv');
   NCicTypeChecker.typeof status subst metasenv ctx ty
;;
  
let type0= NUri.uri_of_string ("cic:/matita/pts/Type0.univ")
;;

let perforate_small status subst metasenv context t =
  let rec aux = function
    | NCic.Appl (hd::tl) ->
	let map t =
	    let s = sort_of status subst metasenv context t in
	    match s with
	      | NCic.Sort(NCic.Type [`Type,u])
		  when u=type0 -> NCic.Meta (0,(0,NCic.Irl 0))
	      | _ -> aux t
	in
	  NCic.Appl (hd::List.map map tl)
    | t -> t
  in 
    aux t
;;

let get_cands retrieve_for diff empty gty weak_gty =
  let cands = retrieve_for gty in
    match weak_gty with
      | None -> cands, empty
      | Some weak_gty ->
          let more_cands =  retrieve_for weak_gty in
            cands, diff more_cands cands
;;

let get_candidates ?(smart=true) ~pfailed depth flags status cache signature gty =
  let universe = status#auto_cache in
  let _,_,metasenv,subst,_ = status#obj in
  let context = ctx_of gty in
  let _, raw_gty = term_of_cic_term status gty context in
  let is_prod, is_eq =   
  let status, t = term_of_cic_term status gty context  in 
  let t = NCicReduction.whd status subst context t in
    match t with
      | NCic.Prod _ -> true, false
      | _ -> false, NCicParamod.is_equation status metasenv subst context t 
  in
  debug_print ~depth (lazy ("gty:" ^ NTacStatus.ppterm status gty));
  let is_eq = 
    NCicParamod.is_equation status metasenv subst context raw_gty 
  in
  let raw_weak_gty, weak_gty  =
    if smart then
      match raw_gty with
	| NCic.Appl _ 
	| NCic.Const _ 
	| NCic.Rel _ -> 
            let raw_weak = 
              perforate_small status subst metasenv context raw_gty in
            let weak = mk_cic_term context raw_weak in
            noprint ~depth (lazy ("weak_gty:" ^ NTacStatus.ppterm status weak));
              Some raw_weak, Some (weak)
	| _ -> None,None
    else None,None
  in
  (* we now compute global candidates *)
  let global_cands, smart_global_cands =
    let mapf s = 
      let to_ast = function 
        | NCic.Const r when true 
             (*is_relevant statistics r*) -> Some (Ast.NRef r)
     (* | NCic.Const _ -> None  *)
	| _ -> assert false in
	  HExtlib.filter_map 
	    to_ast (NDiscriminationTree.TermSet.elements s) in
      let g,l = 
	get_cands
	  (NDiscriminationTree.DiscriminationTree.retrieve_unifiables universe)
	  NDiscriminationTree.TermSet.diff 
	  NDiscriminationTree.TermSet.empty
	  raw_gty raw_weak_gty in
      mapf g, mapf l in
  (* we now compute local candidates *)
  let local_cands,smart_local_cands = 
    let mapf s = 
      let to_ast t =
	let _status, t = term_of_cic_term status t context 
	in Ast.NCic t in
	List.map to_ast (Ncic_termSet.elements s) in
    let g,l = 
      get_cands
	(fun ty -> search_in_th ty cache)
	Ncic_termSet.diff  Ncic_termSet.empty gty weak_gty in
      mapf g, mapf l in
  (* we now splits candidates in facts or not facts *)
  let test = is_a_fact_ast status subst metasenv context in
  let by,given_candidates =
    match flags.candidates with
    | Some l -> true, l
    | None -> false, [] in
(* we compute candidates to be applied in normal mode, splitted in
     facts and not facts *)
  let candidates_facts,candidates_other =
    let gl1,gl2 = List.partition test global_cands in
    let ll1,ll2 = List.partition test local_cands in
    (* if the goal is an equation and paramodulation did not fail
     we avoid to apply unit equalities; refl is an
     exception since it prompts for convertibility *)
    let l1 = if is_eq && (not pfailed) 
      then [Ast.Ident("refl",None)] else gl1@ll1 in 
    let l2 = 
      (* if smart given candidates are applied in smart mode *)
      if by && smart then ll2
      else if by then given_candidates@ll2 
      else gl2@ll2
    in l1,l2
  in
  (* we now compute candidates to be applied in smart mode, splitted in
     facts and not facts *) 
  let smart_candidates_facts, smart_candidates_other =
    if is_prod || not(smart) then [],[] 
    else 
    let sgl1,sgl2 = List.partition test smart_global_cands in
    let sll1,sll2 = List.partition test smart_local_cands in
    let l1 = if is_eq then [] else sgl1@sll1 in
    let l2 = 
      if by && smart then given_candidates@sll2 
      else if by then sll2
      else sgl2@sll2
    in l1,l2
  in
  candidates_facts,
  smart_candidates_facts,
  sort_candidates status context (candidates_other),
  sort_candidates status context (smart_candidates_other)
;;

let applicative_case ~pfailed depth signature status flags gty cache =
  app_counter:= !app_counter+1; 
  let _,_,metasenv,subst,_ = status#obj in
  let context = ctx_of gty in
  let tcache = cache.facts in
  let is_prod, is_eq =   
    let status, t = term_of_cic_term status gty context  in 
    let t = NCicReduction.whd status subst context t in
      match t with
	| NCic.Prod _ -> true, false
	| _ -> false, NCicParamod.is_equation status metasenv subst context t 
  in
  debug_print ~depth (lazy (string_of_bool is_eq)); 
  (* new *)
  let candidates_facts, smart_candidates_facts, 
      candidates_other, smart_candidates_other = 
    get_candidates ~smart:true ~pfailed depth 
      flags status tcache signature gty 
  in
  let sm = if is_eq || is_prod then 0 else 2 in
  let sm1 = if flags.last then 2 else 0 in 
  let maxd = (depth + 1 = flags.maxdepth) in 
  let try_candidates only_one sm acc candidates =
    List.fold_left 
      (fun elems cand ->
         if (only_one && (elems <> [])) then elems 
         else
           match try_candidate (~smart:sm) 
             flags depth status cache.unit_eq context cand with
               | None -> elems
               | Some x -> x::elems)
      acc candidates
  in 
  (* if the goal is the last one we stop at the first fact *)
  let elems = try_candidates flags.last sm [] candidates_facts in
  (* now we add smart_facts *)
  let elems = try_candidates flags.last sm elems smart_candidates_facts in
  (* if we are at maxdepth and the goal is not a product we are done 
     similarly, if the goal is the last one and we already found a
     solution *)
  if (maxd && not(is_prod)) || (flags.last && elems<>[]) then elems
  else
    let elems = try_candidates false 2 elems candidates_other in
    debug_print ~depth (lazy ("not facts: try smart application"));
    try_candidates false 2 elems smart_candidates_other
;;

exception Found
;;

(* gty is supposed to be meta-closed *)
let is_subsumed depth filter_depth status gty cache =
  if cache=[] then false else (
  debug_print ~depth (lazy("Subsuming " ^ (ppterm status gty))); 
  let n,h,metasenv,subst,obj = status#obj in
  let ctx = ctx_of gty in
  let _ , raw_gty = term_of_cic_term status gty ctx in
  let target = NCicSubstitution.lift status 1 raw_gty in 
  (* we compute candidates using the perforated type *)
  let weak_gty  =
    match target with
      | NCic.Appl _ 
      | NCic.Const _ 
      | NCic.Rel _ -> 
          let raw_weak = 
            perforate_small status subst metasenv ctx raw_gty in
          let weak = mk_cic_term ctx raw_weak in
          debug_print ~depth (lazy ("weak_gty:" ^ NTacStatus.ppterm status weak));
          Some (weak)
      | _ -> None
  in
  (* candidates must only be searched w.r.t the given context *)
  let candidates = 
    try
    let idx = List.assq ctx cache in
    match weak_gty with
      | Some weak ->
          Ncic_termSet.elements 
            (InvRelDiscriminationTree.retrieve_unifiables idx weak)
      |None -> []
    with Not_found -> []
  in
  (* this is a dirty trick: the first argument of an application is used
     to remember at which depth a goal failed *)
  let filter t = 
    let ctx = ctx_of t in 
    let _, src = term_of_cic_term status t ctx in 
    match src with 
     | NCic.Appl [NCic.Implicit (`Typeof d); t] 
       when d <= depth -> Some (mk_cic_term ctx t)
     | _ -> None in
  let candidates = 
    if filter_depth then HExtlib.filter_map filter candidates else candidates in  
  debug_print ~depth
    (lazy ("failure candidates: " ^ string_of_int (List.length candidates)));
    try
      List.iter
        (fun t ->
           let _ , source = term_of_cic_term status t ctx in
           let implication = 
             NCic.Prod("foo",source,target) in
           let metasenv,j,_,_ = 
             NCicMetaSubst.mk_meta  
               metasenv ctx ~with_type:implication `IsType in
           let status = status#set_obj (n,h,metasenv,subst,obj) in
           let status = status#set_stack [([1,Open j],[],[],`NoTag)] in 
           try
             let status = NTactics.intro_tac "foo" status in
             let status =
               NTactics.apply_tac ("",0,Ast.NCic (NCic.Rel 1)) status
             in 
               if (head_goals status#stack = []) then raise Found
               else ()
           with
             | Error _ -> ())
        candidates;false
    with Found -> debug_print ~depth (lazy "success");true)
;;

let rec guess_name name ctx = 
  if name = "_" then guess_name "auto" ctx else
  if not (List.mem_assoc name ctx) then name else
  guess_name (name^"'") ctx
;;

let is_prod status = 
  let _, ctx, gty = current_goal status in
  let status, gty = apply_subst status ctx gty in
  let _, raw_gty = term_of_cic_term status gty ctx in
  match raw_gty with
    | NCic.Prod (name,src,_) ->
        let status, src = whd status ~delta:0 ctx (mk_cic_term ctx src) in 
        (match snd (term_of_cic_term status src ctx) with
        | NCic.Const(NReference.Ref (_,NReference.Ind _) as r) 
        | NCic.Appl (NCic.Const(NReference.Ref (_,NReference.Ind _) as r)::_) ->
            let _,_,itys,_,_ = NCicEnvironment.get_checked_indtys status r in
            (match itys with
            (* | [_,_,_,[_;_]]  con nat va, ovviamente, in loop *)
            | [_,_,_,[_]] 
            | [_,_,_,[]] -> `Inductive (guess_name name ctx)         
            | _ -> `Some (guess_name name ctx))
        | _ -> `Some (guess_name name ctx))
    | _ -> `None

let intro ~depth status facts name =
  let status = NTactics.intro_tac name status in
  let _, ctx, ngty = current_goal status in
  let t = mk_cic_term ctx (NCic.Rel 1) in
  let status, keys = keys_of_term status t in
  let facts = List.fold_left (add_to_th t) facts keys in
    debug_print ~depth (lazy ("intro: "^ name));
  (* unprovability is not stable w.r.t introduction *)
  status, facts
;;

let rec intros_facts ~depth status facts =
  if List.length (head_goals status#stack) <> 1 then status, facts else
  match is_prod status with
    | `Inductive name 
    | `Some(name) ->
        let status,facts =
          intro ~depth status facts name
        in intros_facts ~depth status facts
(*    | `Inductive name ->
          let status = NTactics.case1_tac name status in
          intros_facts ~depth status facts *)
    | _ -> status, facts
;; 

let intros ~depth status cache =
    match is_prod status with
      | `Inductive _
      | `Some _ ->
	  let trace = cache.trace in
          let status,facts =
            intros_facts ~depth status cache.facts 
          in 
          if head_goals status#stack = [] then 
            let status = NTactics.merge_tac status in
            [(0,Ast.Ident("__intros",None)),status], cache
          else
            (* we reindex the equation from scratch *)
            let unit_eq = index_local_equations status#eq_cache status in
            let status = NTactics.merge_tac status in
            [(0,Ast.Ident("__intros",None)),status], 
            init_cache ~facts ~unit_eq () ~trace
      | _ -> [],cache
;;

let reduce ~whd ~depth status g = 
  let n,h,metasenv,subst,o = status#obj in 
  let attr, ctx, ty = NCicUtils.lookup_meta g metasenv in
  let ty = NCicUntrusted.apply_subst status subst ctx ty in
  let ty' =
   (if whd then NCicReduction.whd else NCicTacReduction.normalize) status ~subst ctx ty
  in
  if ty = ty' then []
  else
    (debug_print ~depth 
      (lazy ("reduced to: "^ status#ppterm ctx subst metasenv ty'));
    let metasenv = 
      (g,(attr,ctx,ty'))::(List.filter (fun (i,_) -> i<>g) metasenv) 
    in
    let status = status#set_obj (n,h,metasenv,subst,o) in
    (* we merge to gain a depth level; the previous goal level should
       be empty *)
    let status = NTactics.merge_tac status in
    incr candidate_no;
    [(!candidate_no,Ast.Ident("__whd",None)),status])
;;

let is_meta status gty =
  let _, ty = term_of_cic_term status gty (ctx_of gty) in
  match ty with
  | NCic.Meta _ -> true
  | _ -> false 
;;

let do_something signature flags status g depth gty cache =
  (* if the goal is meta we close it with I:True. This should work
    thanks to the toplogical sorting of goals. *)
  if is_meta status gty then
    let t = Ast.Ident("I",None) in
    debug_print (lazy ("using default term" ^ (NotationPp.pp_term status) t));
    let s = NTactics.apply_tac ("",0,t) status in
    [(0,t),s], cache
  else 
  let l0, cache = intros ~depth status cache in
  if l0 <> [] then l0, cache
  else
  (* whd *)
  let l = reduce ~whd:true ~depth status g in
  (* if l <> [] then l,cache else *)
  (* backward aplications *)
  let l1 = 
    List.map 
      (fun s ->
         incr candidate_no;
         ((!candidate_no,Ast.Ident("__paramod",None)),s))
      (auto_eq_check cache.unit_eq status) 
  in
  let l2 = 
    if ((l1 <> []) && flags.last) then [] else
    applicative_case ~pfailed:(l1=[]) depth signature status flags gty cache 
  in
  (* statistics *)
  List.iter 
    (fun ((_,t),_) -> toref incr_nominations statistics t) l2;
  (* states in l1 have have an empty set of subgoals: no point to sort them *)
  debug_print ~depth 
    (lazy ("alternatives = " ^ (string_of_int (List.length (l1@l@l2)))));
    (* we order alternatives w.r.t the number of subgoals they open *)
    l1 @ (sort_new_elems l2) @ l, cache 
;;

let pp_goal = function
  | (_,Continuationals.Stack.Open i) 
  | (_,Continuationals.Stack.Closed i) -> string_of_int i 
;;

let pp_goals status l =
  String.concat ", " 
    (List.map 
       (fun i -> 
          let gty = get_goalty status i in
            NTacStatus.ppterm status gty)
       l)
;;

module M = 
  struct 
    type t = int
    let compare = Pervasives.compare
  end
;;

module MS = HTopoSort.Make(M)
;;

let sort_tac status =
  let gstatus = 
    match status#stack with
    | [] -> assert false
    | (goals, t, k, tag) :: s ->
        let g = head_goals status#stack in
        let sortedg = 
          (List.rev (MS.topological_sort g (deps status))) in
          noprint (lazy ("old g = " ^ 
            String.concat "," (List.map string_of_int g)));
          noprint (lazy ("sorted goals = " ^ 
            String.concat "," (List.map string_of_int sortedg)));
          let is_it i = function
            | (_,Continuationals.Stack.Open j ) 
            | (_,Continuationals.Stack.Closed j ) -> i = j
          in 
          let sorted_goals = 
            List.map (fun i -> List.find (is_it i) goals) sortedg
          in
            (sorted_goals, t, k, tag) :: s
  in
   status#set_stack gstatus
;;
  
let clean_up_tac status =
  let gstatus = 
    match status#stack with
    | [] -> assert false
    | (g, t, k, tag) :: s ->
        let is_open = function
          | (_,Continuationals.Stack.Open _) -> true
          | (_,Continuationals.Stack.Closed _) -> false
        in
        let g' = List.filter is_open g in
          (g', t, k, tag) :: s
  in
   status#set_stack gstatus
;;

let focus_tac focus status =
  let gstatus = 
    match status#stack with
    | [] -> assert false
    | (g, t, k, tag) :: s ->
        let in_focus = function
          | (_,Continuationals.Stack.Open i) 
          | (_,Continuationals.Stack.Closed i) -> List.mem i focus
        in
        let focus,others = List.partition in_focus g
        in
          (* we need to mark it as a BranchTag, otherwise cannot merge later *)
          (focus,[],[],`BranchTag) :: (others, t, k, tag) :: s
  in
   status#set_stack gstatus
;;

let deep_focus_tac level focus status =
  let in_focus = function
    | (_,Continuationals.Stack.Open i) 
    | (_,Continuationals.Stack.Closed i) -> List.mem i focus
  in
  let rec slice level gs = 
    if level = 0 then [],[],gs else
      match gs with 
	| [] -> assert false
	| (g, t, k, tag) :: s ->
            let f,o,gs = slice (level-1) s in           
            let f1,o1 = List.partition in_focus g
            in
            (f1,[],[],`BranchTag)::f, (o1, t, k, tag)::o, gs
  in
  let gstatus = 
    let f,o,s = slice level status#stack in f@o@s
  in
   status#set_stack gstatus
;;

let move_to_side level status =
match status#stack with
  | [] -> assert false
  | (g,_,_,_)::tl ->
      let is_open = function
          | (_,Continuationals.Stack.Open i) -> Some i
          | (_,Continuationals.Stack.Closed _) -> None
        in 
      let others = menv_closure status (stack_goals (level-1) tl) in
      List.for_all (fun i -> IntSet.mem i others) 
	(HExtlib.filter_map is_open g)

let top_cache ~depth top status cache =
  if top then
    let unit_eq = index_local_equations status#eq_cache status in 
    {cache with unit_eq = unit_eq}
  else cache

let rec auto_clusters ?(top=false)  
    flags signature cache depth status : unit =
  debug_print ~depth (lazy ("entering auto clusters at depth " ^
			   (string_of_int depth)));
  debug_print ~depth (pptrace status cache.trace);
  (* ignore(Unix.select [] [] [] 0.01); *)
  let status = clean_up_tac status in
  let goals = head_goals status#stack in
  if goals = [] then 
    if depth = 0 then raise (Proved (status, cache.trace))
    else 
      let status = NTactics.merge_tac status in
        let cache =
        let l,tree = cache.under_inspection in
  	  match l with 
	    | [] -> cache (* possible because of intros that cleans the cache *)
	    | a::tl -> let tree = rm_from_th a tree a in
	      {cache with under_inspection = tl,tree} 
        in 
         auto_clusters flags signature cache (depth-1) status
  else if List.length goals < 2 then
    let cache = top_cache ~depth top status cache in
    auto_main flags signature cache depth status
  else
    let all_goals = open_goals (depth+1) status in
    debug_print ~depth (lazy ("goals = " ^ 
      String.concat "," (List.map string_of_int all_goals)));
    let classes = HExtlib.clusters (deps status) all_goals in
    (* if any of the classes exceed maxwidth we fail *)
    List.iter
      (fun gl ->
         if List.length gl > flags.maxwidth then 
           begin
	     debug_print ~depth (lazy "FAIL GLOBAL WIDTH"); 
	     HLog.warn (sprintf "global width (%u) exceeded: %u"
	       flags.maxwidth (List.length gl));
	     raise (Gaveup cache.failures)
	   end else ()) classes;
    if List.length classes = 1 then
      let flags = 
        {flags with last = (List.length all_goals = 1)} in 
	(* no need to cluster *)
      let cache = top_cache ~depth top status cache in
        auto_main flags signature cache depth status 
    else
      let classes = if top then List.rev classes else classes in
      debug_print ~depth
        (lazy 
           (String.concat "\n" 
           (List.map
             (fun l -> 
               ("cluster:" ^ String.concat "," (List.map string_of_int l)))
           classes)));
      (* we now process each cluster *)
      let status,cache,b = 
        List.fold_left
          (fun (status,cache,b) gl ->
             let flags = 
               {flags with last = (List.length gl = 1)} in 
             let lold = List.length status#stack in 
	      debug_print ~depth (lazy ("stack length = " ^ 
			(string_of_int lold)));
             let fstatus = deep_focus_tac (depth+1) gl status in
             let cache = top_cache ~depth top fstatus cache in
             try 
               debug_print ~depth (lazy ("focusing on" ^ 
                              String.concat "," (List.map string_of_int gl)));
               auto_main flags signature cache depth fstatus; assert false
             with 
               | Proved(status,trace) -> 
		   let status = NTactics.merge_tac status in
	           let cache = {cache with trace = trace} in
		   let lnew = List.length status#stack in 
		     assert (lold = lnew);
		   (status,cache,true)
               | Gaveup failures when top ->
                   let cache = {cache with failures = failures} in
                   (status,cache,b)
          )
          (status,cache,false) classes
      in
      let rec final_merge n s =
	if n = 0 then s else final_merge (n-1) (NTactics.merge_tac s)
      in let status = final_merge depth status 
      in if b then raise (Proved(status,cache.trace)) else raise (Gaveup cache.failures)

and
        
(* BRAND NEW VERSION *)         
auto_main flags signature cache depth status: unit =
  debug_print ~depth (lazy "entering auto main");
  debug_print ~depth (pptrace status cache.trace);
  debug_print ~depth (lazy ("stack length = " ^ 
			(string_of_int (List.length status#stack))));
  (* ignore(Unix.select [] [] [] 0.01); *)
  let status = sort_tac (clean_up_tac status) in
  let goals = head_goals status#stack in
  match goals with
    | [] when depth = 0 -> raise (Proved (status,cache.trace))
    | []  -> 
	let status = NTactics.merge_tac status in
	let cache =
	  let l,tree = cache.under_inspection in
	    match l with 
	      | [] -> cache (* possible because of intros that cleans the cache *)
	      | a::tl -> let tree = rm_from_th a tree a in
		  {cache with under_inspection = tl,tree} 
	in 
	  auto_clusters flags signature cache (depth-1) status
    | orig::_ ->
	if depth > 0 && move_to_side depth status
	then 
	  let status = NTactics.merge_tac status in
	  let cache =
	    let l,tree = cache.under_inspection in
	      match l with 
	        | [] -> cache (* possible because of intros that cleans the cache*)
	        | a::tl -> let tree = rm_from_th a tree a in
		    {cache with under_inspection = tl,tree} 
	  in 
	    auto_clusters flags signature cache (depth-1) status 
	else
        let ng = List.length goals in
        (* moved inside auto_clusters *)
        if ng > flags.maxwidth then begin 
          debug_print ~depth (lazy "FAIL LOCAL WIDTH");
	  HLog.warn (sprintf "local width (%u) exceeded: %u"
	     flags.maxwidth ng);
	  raise (Gaveup cache.failures)
        end else if depth = flags.maxdepth then
	  raise (Gaveup cache.failures)
        else 
        let status = NTactics.branch_tac ~force:true status in
        let g,gctx, gty = current_goal status in
        let ctx,ty = close status g in
        let closegty = mk_cic_term ctx ty in
        let status, gty = apply_subst status gctx gty in
        debug_print ~depth (lazy("Attacking goal " ^ 
          string_of_int g ^ " : "^ppterm status gty));
        debug_print ~depth (lazy ("current failures: " ^ 
          string_of_int (List.length (all_elements ctx cache.failures))));
        let is_eq =
           let _,_,metasenv,subst,_ = status#obj in
           NCicParamod.is_equation status metasenv subst ctx ty in
        (* if the goal is an equality we artificially raise its depth up to
           flags.maxdepth - 1 *)
        if (not flags.last && is_eq && (depth < (flags.maxdepth -2))) then
        (* for efficiency reasons, in this case we severely cripple the
           search depth *)
          (debug_print ~depth (lazy ("RAISING DEPTH TO " ^ string_of_int (depth+1)));
           auto_main flags signature cache (depth+1) status)
        (* check for loops *)
        else if is_subsumed depth false status closegty (snd cache.under_inspection) then 
          (debug_print ~depth (lazy "SUBSUMED");
           raise (Gaveup cache.failures))
        (* check for failures *)
        else if is_subsumed depth true status closegty cache.failures then 
          (debug_print ~depth (lazy "ALREADY MET");
           raise (Gaveup cache.failures))
        else
	let new_sig = height_of_goal g status in
        if new_sig < signature then 
	  (debug_print  ~depth (lazy ("news = " ^ (string_of_int new_sig)));
	   debug_print  ~depth (lazy ("olds = " ^ (string_of_int signature)))); 
        let alternatives, cache = 
          do_something signature flags status g depth gty cache in
        let loop_cache =
          if flags.last then
	    let l,tree = cache.under_inspection in
	    let l,tree = closegty::l, add_to_th closegty tree closegty in
            {cache with under_inspection = l,tree}
          else cache in 
        let failures =
          List.fold_left  
          (fun allfailures ((_,t),status) ->
             debug_print ~depth 
	       (lazy ("(re)considering goal " ^ 
		       (string_of_int g) ^" : "^ppterm status gty)); 
             debug_print (~depth:depth) 
               (lazy ("Case: " ^ NotationPp.pp_term status t));
             let depth,cache =
	       if t=Ast.Ident("__whd",None) || 
                  t=Ast.Ident("__intros",None) 
               then depth, cache 
	       else depth+1,loop_cache in 
	     let cache = add_to_trace status ~depth cache t in
             let cache = {cache with failures = allfailures} in
	     try
	       auto_clusters flags signature cache depth status;
               assert false;
	     with Gaveup fail ->
	       debug_print ~depth (lazy "Failed");
	       fail)
	  cache.failures alternatives in
        let failures =
          if flags.last then 
            let newfail =
              let dty = NCic.Appl [NCic.Implicit (`Typeof depth); ty] in
              mk_cic_term ctx dty 
            in 
            (*prerr_endline ("FAILURE : " ^ ppterm status gty);*)
            add_to_th newfail failures closegty
          else failures in
        debug_print ~depth (lazy "no more candidates");
	raise (Gaveup failures)
;;

let int name l def = 
  try int_of_string (List.assoc name l)
  with Failure _ | Not_found -> def
;;

module AstSet = Set.Make(struct type t = Ast.term let compare = compare end)

let cleanup_trace s trace =
  (* removing duplicates *)
  let trace_set = 
    List.fold_left 
      (fun acc t -> AstSet.add t acc)
      AstSet.empty trace in
  let trace = AstSet.elements trace_set
    (* filtering facts *)
  in List.filter 
       (fun t -> 
	  match t with
	    | Ast.NRef (NReference.Ref (u,_)) -> not (is_a_fact_obj s u)
	    | _ -> false) trace
;;

let auto_tac ~params:(univ,flags) ?(trace_ref=ref []) status =
  let oldstatus = status in
  let status = (status:> NTacStatus.tac_status) in
  let goals = head_goals status#stack in
  let status, facts = mk_th_cache status goals in
(*  let unit_eq = index_local_equations status#eq_cache status in *)
  let cache = init_cache ~facts () in 
(*   pp_th status facts; *)
(*
  NDiscriminationTree.DiscriminationTree.iter status#auto_cache (fun p t -> 
    debug_print (lazy(
      NDiscriminationTree.NCicIndexable.string_of_path p ^ " |--> " ^
      String.concat "\n    " (List.map (
      status#ppterm ~metasenv:[] ~context:[] ~subst:[])
        (NDiscriminationTree.TermSet.elements t))
      )));
*)
  let candidates = 
    match univ with
      | None -> None 
      | Some l -> 
	  let to_Ast t =
(* FG: `XTSort here? *)	  
	    let status, res = disambiguate status [] t `XTNone in 
	    let _,res = term_of_cic_term status res (ctx_of res) 
	    in Ast.NCic res 
          in Some (List.map to_Ast l) 
  in
  let depth = int "depth" flags 3 in 
  let size  = int "size" flags 10 in 
  let width = int "width" flags 4 (* (3+List.length goals)*) in 
  (* XXX fix sort *)
(*   let goals = List.map (fun i -> (i,P)) goals in *)
  let signature = height_of_goals status in 
  let flags = { 
          last = true;
          candidates = candidates;
          maxwidth = width;
          maxsize = size;
          maxdepth = depth;
          timeout = Unix.gettimeofday() +. 3000.;
          do_types = false; 
  } in
  let initial_time = Unix.gettimeofday() in
  app_counter:= 0;
  let rec up_to x y =
    if x > y then
      (debug_print(lazy
        ("TIME ELAPSED:"^string_of_float(Unix.gettimeofday()-.initial_time)));
       debug_print(lazy
        ("Applicative nodes:"^string_of_int !app_counter)); 
       raise (Error (lazy "auto gave up", None)))
    else
      let _ = debug_print (lazy("\n\nRound "^string_of_int x^"\n")) in
      let flags = { flags with maxdepth = x } 
      in 
        try auto_clusters (~top:true) flags signature cache 0 status;assert false 
(*
        try auto_main flags signature cache 0 status;assert false
*)
        with
          | Gaveup _ -> up_to (x+1) y
          | Proved (s,trace) -> 
              debug_print (lazy ("proved at depth " ^ string_of_int x));
	      List.iter (toref incr_uses statistics) trace;
              let trace = cleanup_trace s trace in
	      let _ = debug_print (pptrace status trace) in
              let stack = 
                match s#stack with
                  | (g,t,k,f) :: rest -> (filter_open g,t,k,f):: rest
                  | _ -> assert false
              in
              let s = s#set_stack stack in
                trace_ref := trace;
                oldstatus#set_status s 
  in
  let s = up_to depth depth in
    debug_print (print_stat status statistics);
    debug_print(lazy
        ("TIME ELAPSED:"^string_of_float(Unix.gettimeofday()-.initial_time)));
    debug_print(lazy
        ("Applicative nodes:"^string_of_int !app_counter));
    s
;;

let auto_tac ~params:(_,flags as params) ?trace_ref =
  if List.mem_assoc "demod" flags then 
    demod_tac ~params 
  else if List.mem_assoc "paramod" flags then 
    paramod_tac ~params 
  else if List.mem_assoc "fast_paramod" flags then 
    fast_eq_check_tac ~params  
  else auto_tac ~params ?trace_ref
;;




















