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

(* $Id: nCicUnification.ml 12479 2013-02-01 13:47:25Z fguidi $ *)

exception UnificationFailure of string Lazy.t;;
exception Uncertain of string Lazy.t;;
exception AssertFailure of string Lazy.t;;
exception KeepReducing of string Lazy.t;;
exception KeepReducingThis of 
  string Lazy.t * (NCicReduction.machine * bool) * 
                  (NCicReduction.machine * bool) ;;

let (===) x y = Pervasives.compare x y = 0 ;;

let mk_msg (status:#NCic.status) metasenv subst context t1 t2 =
 (lazy (
  "Can't unify " ^ status#ppterm ~metasenv ~subst ~context t1 ^
  " with " ^ status#ppterm ~metasenv ~subst ~context t2))

let mk_appl status ~upto hd tl =
  NCicReduction.head_beta_reduce status ~upto
    (match hd with
    | NCic.Appl l -> NCic.Appl (l@tl)
    | _ -> NCic.Appl (hd :: tl))
;;

exception WrongShape;;

let eta_reduce status subst t = 
  let delift_if_not_occur body =
    try 
        Some (NCicSubstitution.psubst status ~avoid_beta_redexes:true
          (fun () -> raise WrongShape) [()] body)
    with WrongShape -> None
  in 
  let rec eat_lambdas ctx = function
    | NCic.Lambda (name, src, tgt) -> 
        eat_lambdas ((name, src) :: ctx) tgt
    | NCic.Meta (i,lc) as t->
        (try 
          let _,_,t,_ = NCicUtils.lookup_subst i subst in
          let t = NCicSubstitution.subst_meta status lc t in
          eat_lambdas ctx t
        with NCicUtils.Subst_not_found _ -> ctx, t)
    | t -> ctx, t
  in
  let context_body = eat_lambdas [] t in
  let rec aux = function
    | [],body -> body
    | (name, src)::ctx, (NCic.Appl (hd::[NCic.Rel 1]) as bo) -> 
        (match delift_if_not_occur hd with
        | None -> aux (ctx,NCic.Lambda(name,src, bo)) 
        | Some bo -> aux (ctx,bo))
    | (name, src)::ctx, (NCic.Appl args as bo) 
      when HExtlib.list_last args = NCic.Rel 1 -> 
        let args, _ = HExtlib.split_nth (List.length args - 1) args in
        (match delift_if_not_occur (NCic.Appl args) with
        | None -> aux (ctx,NCic.Lambda(name,src, bo)) 
        | Some bo -> aux (ctx,bo))
    | (name, src) :: ctx, t ->
        aux (ctx,NCic.Lambda(name,src, t)) 
  in
    aux context_body
;;

module C = NCic;;
module Ref = NReference;;

let debug = ref false;;
let indent = ref "";;
let times = ref [];;
let pp s =
 if !debug then
  prerr_endline (Printf.sprintf "%-20s" !indent ^ " " ^ Lazy.force s)
;;
let inside c =
 if !debug then
  begin
   let time1 = Unix.gettimeofday () in
   indent := !indent ^ String.make 1 c;
   times := time1 :: !times;
   prerr_endline ("{{{" ^ !indent ^ " ")
  end
;;
let outside exc_opt =
 if !debug then
  begin
   let time2 = Unix.gettimeofday () in
   let time1 =
    match !times with time1::tl -> times := tl; time1 | [] -> assert false in
   prerr_endline ("}}} " ^ !indent ^ " " ^ string_of_float (time2 -. time1));
   (match exc_opt with
   | Some (UnificationFailure msg) ->  prerr_endline ("exception raised: NCicUnification.UnificationFailure:" ^ Lazy.force msg)
   | Some (Uncertain msg) ->  prerr_endline ("exception raised: NCicUnification.Uncertain:" ^ Lazy.force msg)
   | Some e ->  prerr_endline ("exception raised: " ^ Printexc.to_string e)
   | None -> ());
   try
    indent := String.sub !indent 0 (String.length !indent -1)
   with
    Invalid_argument _ -> indent := "??"; ()
  end
;;

let ppcontext status ~metasenv ~subst c = 
      "\nctx:\n"^ status#ppcontext ~metasenv ~subst c
;;
let ppmetasenv status ~subst m = "\nmenv:\n" ^ status#ppmetasenv ~subst m;;

let ppcontext _status ~metasenv:_metasenv ~subst:_subst _context = "";;
let ppmetasenv _status ~subst:_subst _metasenv = "";;
let ppterm (status:#NCic.status) ~metasenv ~subst ~context = status#ppterm ~metasenv ~subst ~context;;
(* let ppterm status ~metasenv:_ ~subst:_ ~context:_ _ = "";; *)

let is_locked n subst =
   try
     match NCicUtils.lookup_subst n subst with
     | tag, _,_,_ when NCicMetaSubst.is_out_scope_tag tag -> true
     | _ -> false
   with NCicUtils.Subst_not_found _ -> false
;;

let rec mk_irl stop base =
  if base > stop then []
  else (NCic.Rel base) :: mk_irl stop (base+1) 
;;

(* the argument must be a term in whd *)
let rec could_reduce status ~subst context =
 function
  | C.Meta _ -> true
  | C.Appl (C.Const (Ref.Ref (_,Ref.Fix (_,recno,_)))::args)
     when List.length args > recno ->
      let t = NCicReduction.whd status ~subst context (List.nth args recno) in
        could_reduce status ~subst context t
  | C.Match (_,_,he,_) ->
     let he = NCicReduction.whd status ~subst context he in
      could_reduce status ~subst context he
  | C.Appl (he::_) -> could_reduce status ~subst context he
  | C.Sort _ | C.Rel _ | C.Prod _ | C.Lambda _ | C.Const _ -> false
  | C.Appl [] | C.LetIn _ | C.Implicit _ -> assert false
;;

let rec lambda_intros status metasenv subst context argsno ty =
 pp (lazy ("LAMBDA INTROS: " ^ ppterm status ~metasenv ~subst ~context ty));
 match argsno with
    0 -> 
       let metasenv, _, bo, _ = 
         NCicMetaSubst.mk_meta metasenv context ~with_type:ty `IsTerm
       in
       metasenv, bo
  | _ ->
     (match NCicReduction.whd status ~subst context ty with
         C.Prod (n,so,ta) ->
          let metasenv,bo =
           lambda_intros status metasenv subst
            ((n,C.Decl so)::context) (argsno - 1) ta
          in
           metasenv,C.Lambda (n,so,bo)
       | _ -> assert false)
;;
  
let unopt exc = function None -> raise exc | Some x -> x ;;

let fix (status:#NCic.status) metasenv subst is_sup test_eq_only exc t =
  (*D*)  inside 'f'; try let rc =  
  pp (lazy (status#ppterm ~metasenv ~subst ~context:[] t));
  let rec aux test_eq_only metasenv = function
    | NCic.Prod (n,so,ta) ->
       let metasenv,so = aux true metasenv so in
       let metasenv,ta = aux test_eq_only metasenv ta in
        metasenv,NCic.Prod (n,so,ta)
    | NCic.Sort (NCic.Type [(`CProp|`Type),_]) as orig when test_eq_only ->
       metasenv,orig
    | NCic.Sort (NCic.Type _) when test_eq_only -> raise exc
    | NCic.Sort (NCic.Type u) when is_sup ->
       metasenv, NCic.Sort (NCic.Type (unopt exc (NCicEnvironment.sup u)))
    | NCic.Sort (NCic.Type u) ->
       metasenv, NCic.Sort (NCic.Type 
         (unopt exc (NCicEnvironment.inf ~strict:false u)))
    | NCic.Meta (n,_) as orig ->
        (try 
          let _,_,_,_ = NCicUtils.lookup_subst n subst in metasenv,orig
         with NCicUtils.Subst_not_found _ -> 
          let metasenv, _ = NCicMetaSubst.extend_meta metasenv n in
           metasenv, orig)
    | t ->
      NCicUntrusted.map_term_fold_a status (fun _ x -> x) test_eq_only aux metasenv t
  in
   aux test_eq_only metasenv t
 (*D*)  in outside None; rc with exn -> outside (Some exn); raise exn 
;;

let metasenv_to_subst n (kind,context,ty) metasenv subst =
 let infos,metasenv = List.partition (fun (n',_) -> n = n') metasenv in
 let attrs,octx,oty = match infos with [_,infos] -> infos | _ -> assert false in
 if octx=context && oty=ty then
  (n,(NCicUntrusted.set_kind kind attrs, octx, oty))::metasenv,subst
 else 
  let metasenv, _, bo, _ = 
   NCicMetaSubst.mk_meta metasenv context ~attrs ~with_type:ty kind in
  let subst = (n,(NCicUntrusted.set_kind kind attrs,octx,bo,oty))::subst in
   metasenv,subst
;;

let rec sortfy status exc metasenv subst context t =
 let t = NCicReduction.whd status ~subst context t in
 let metasenv,subst =
  match t with
   | NCic.Sort _ -> metasenv, subst
   | NCic.Meta (n,_) -> 
      let attrs, context, ty = NCicUtils.lookup_meta n metasenv in
      let kind = NCicUntrusted.kind_of_meta attrs in
       if kind = `IsSort then
        metasenv,subst
       else
        (match ty with
          | NCic.Implicit (`Typeof _) ->
              metasenv_to_subst n (`IsSort,[],ty) metasenv subst
          | ty ->
             let metasenv,subst,ty = sortfy status exc metasenv subst context ty in
              metasenv_to_subst n (`IsSort,[],ty) metasenv subst)
   | NCic.Implicit _ -> assert false
   | _ -> raise exc
 in
  metasenv,subst,t

let indfy status exc metasenv subst context t =
 let t = NCicReduction.whd status ~subst context t in
 let metasenv,subst =
  match t with
   | NCic.Const (Ref.Ref (_, Ref.Ind _))
   | NCic.Appl (NCic.Const (Ref.Ref (_, Ref.Ind _))::_) -> metasenv, subst
(*
   | NCic.Meta (n,_) -> 
      let attrs, context, ty = NCicUtils.lookup_meta n metasenv in
      let kind = NCicUntrusted.kind_of_meta attrs in
       if kind = `IsSort then
        metasenv,subst
       else
        (match ty with
          | NCic.Implicit (`Typeof _) ->
              metasenv_to_subst n (`IsSort,[],ty) metasenv subst
          | ty ->
             let metasenv,subst,ty = sortfy status exc metasenv subst context ty in
              metasenv_to_subst n (`IsSort,[],ty) metasenv subst)
*)
   | NCic.Implicit _ -> assert false
   | _ -> raise exc
 in
  metasenv,subst,t

let tipify status exc metasenv subst context t ty =
 let is_type attrs =
  match NCicUntrusted.kind_of_meta attrs with
     `IsType | `IsSort -> true
   | `IsTerm -> false
 in
 let rec optimize_meta metasenv subst =
  function 
     NCic.Meta (n,lc) ->
      (try
        let attrs,_,_ = NCicUtils.lookup_meta n metasenv in
        if is_type attrs then
         metasenv,subst,true
        else
         let _,cc,ty = NCicUtils.lookup_meta n metasenv in
         let metasenv,subst,ty = sortfy status exc metasenv subst cc ty in
         let metasenv = 
           NCicUntrusted.replace_in_metasenv n
            (fun attrs,cc,_ -> NCicUntrusted.set_kind `IsType attrs, cc, ty)
            metasenv 
         in
          metasenv,subst,false
       with
        NCicUtils.Meta_not_found _ ->
         let attrs, _,bo,_ = NCicUtils.lookup_subst n subst in
         if is_type attrs then
          metasenv,subst,true
         else
          let _,cc,_,ty = NCicUtils.lookup_subst n subst in
          let metasenv,subst,ty = sortfy status exc metasenv subst cc ty in
          let subst = 
            NCicUntrusted.replace_in_subst n
              (fun attrs,cc,bo,_->NCicUntrusted.set_kind `IsType attrs,cc,bo,ty)
             subst 
          in
           optimize_meta metasenv subst (NCicSubstitution.subst_meta status lc bo))
   | _ -> metasenv,subst,false
 in
  let metasenv,subst,b = optimize_meta metasenv subst t in
   if b then
    metasenv,subst,t
   else
    let metasenv,subst,_ = sortfy status exc metasenv subst context ty in
     metasenv,subst,t
;;

let put_in_whd status subst context m1 m2 =
  NCicReduction.reduce_machine status ~delta:max_int ~subst context m1,
  NCicReduction.reduce_machine status ~delta:max_int ~subst context m2
;;

let rec instantiate status test_eq_only metasenv subst context n lc t swap =
 (*D*)  inside 'I'; try let rc =  
  pp (lazy(string_of_int n^" :=?= "^ppterm status ~metasenv ~subst ~context t));
  let exc = 
    UnificationFailure (mk_msg status metasenv subst context (NCic.Meta (n,lc)) t) in
  let move_to_subst i ((_,cc,t,_) as infos) metasenv subst =
    let metasenv = List.remove_assoc i metasenv in
    pp(lazy(string_of_int n ^ " :==> "^ ppterm status ~metasenv ~subst ~context:cc t));
    metasenv, (i,infos) :: subst
  in
  let delift_to_subst test_eq_only n lc (attrs,cc,ty) t context metasenv subst =
    pp (lazy(string_of_int n ^ " := 111 = "^ 
      ppterm status ~metasenv ~subst ~context t));
    let (metasenv, subst), t = 
      try 
        NCicMetaSubst.delift status ~unify:(unify_for_delift status)
         metasenv subst context n lc t
      with NCicMetaSubst.Uncertain msg -> 
           pp (lazy ("delift is uncertain: " ^ Lazy.force msg));
           raise (Uncertain msg)
      | NCicMetaSubst.MetaSubstFailure msg -> 
           pp (lazy ("delift fails: " ^ Lazy.force msg));
           raise (UnificationFailure msg)
    in
    pp (lazy(string_of_int n ^ " := 222 = "^
      ppterm status ~metasenv ~subst ~context:cc t^ppmetasenv status ~subst metasenv));
    (* Unifying the types may have already instantiated n. *)
    try
      let _, _,oldt,_ = NCicUtils.lookup_subst n subst in
      let oldt = NCicSubstitution.subst_meta status lc oldt in
      let t = NCicSubstitution.subst_meta status lc t in
      (* conjecture: always fail --> occur check *)
      unify status test_eq_only metasenv subst context t oldt false
    with NCicUtils.Subst_not_found _ -> 
      move_to_subst n (attrs,cc,t,ty) metasenv subst
  in
  let attrs,cc,ty = NCicUtils.lookup_meta n metasenv in
  let kind = NCicUntrusted.kind_of_meta attrs in
  let metasenv,t = fix status metasenv subst swap test_eq_only exc t in
  let ty_t = NCicTypeChecker.typeof status ~metasenv ~subst context t in
  let metasenv,subst,t =
   match kind with
      `IsSort -> sortfy status exc metasenv subst context t
    | `IsType -> tipify status exc metasenv subst context t ty_t
    | `IsTerm -> metasenv,subst,t in
  match kind with
  | `IsSort ->
     (match ty,t with
         NCic.Implicit (`Typeof _), NCic.Sort _ ->
           move_to_subst n (attrs,cc,t,ty_t) metasenv subst  
       | NCic.Sort (NCic.Type u1), NCic.Sort s ->
          let s =
           match s,swap with
              NCic.Type u2, false ->
               NCic.Sort (NCic.Type
                (unopt exc (NCicEnvironment.inf ~strict:false
                 (unopt exc (NCicEnvironment.inf ~strict:true u1) @ u2))))
            | NCic.Type u2, true ->
               if NCicEnvironment.universe_lt u2 u1 then
                NCic.Sort (NCic.Type u2)
               else (raise exc)
            | NCic.Prop,_ -> NCic.Sort NCic.Prop
          in
           move_to_subst n (attrs,cc,s,ty) metasenv subst  
       | NCic.Implicit (`Typeof _), NCic.Meta _ ->
          move_to_subst n (attrs,cc,t,ty_t) metasenv subst  
       | _, NCic.Meta _
       | NCic.Meta _, NCic.Sort _ ->
          pp (lazy ("On the types: " ^
            ppterm status ~metasenv ~subst ~context ty ^ "=<=" ^
            ppterm status ~metasenv ~subst ~context ty_t)); 
          let metasenv, subst = 
            unify status false metasenv subst context ty_t ty false in
          delift_to_subst test_eq_only n lc (attrs,cc,ty) t
           context metasenv subst
       | _ -> assert false)
  | `IsType
  | `IsTerm ->
     (match ty with
         NCic.Implicit (`Typeof _) ->
          let (metasenv, subst), ty_t = 
            try 
              NCicMetaSubst.delift status ~unify:(unify_for_delift status)
               metasenv subst context n lc ty_t
            with NCicMetaSubst.Uncertain msg -> 
                 pp (lazy ("delift is uncertain: " ^ Lazy.force msg));
                 raise (Uncertain msg)
            | NCicMetaSubst.MetaSubstFailure msg -> 
                 pp (lazy ("delift fails: " ^ Lazy.force msg));
                 raise (UnificationFailure msg)
          in
           delift_to_subst test_eq_only n lc (attrs,cc,ty_t) t context metasenv
            subst 
       | _ ->
        let lty = NCicSubstitution.subst_meta status lc ty in
        pp (lazy ("On the types: " ^
          ppterm status ~metasenv ~subst ~context ty_t ^ "=<=" ^
          ppterm status ~metasenv ~subst ~context lty)); 
        let metasenv, subst = 
          unify status false metasenv subst context ty_t lty false
        in
        delift_to_subst test_eq_only n lc (attrs,cc,ty) t context metasenv
         subst)
 (*D*)  in outside None; rc with exn -> outside (Some exn); raise exn 

and fo_unif_w_hints during_delift status swap test_eq_only metasenv subst context (_,t1 as m1) (_,t2 as m2) =
 try fo_unif during_delift status swap test_eq_only metasenv subst context m1 m2
 with 
 | UnificationFailure _ as exn -> raise exn
 | KeepReducing _ | Uncertain _ as exn ->
   let (t1,norm1 as tm1),(t2,norm2 as tm2) =
    put_in_whd status subst context (0,[],t1,[]) (0,[],t2,[])
   in
    match 
      try_hints status swap test_eq_only metasenv subst context
       (norm1,NCicReduction.unwind status t1) (norm2,NCicReduction.unwind status t2)
    with
     | Some x -> x
     | None -> 
         match exn with 
         | KeepReducing msg -> raise (KeepReducingThis (msg,tm1,tm2))
         | Uncertain _ as exn -> raise exn
         | _ -> assert false

and unify_for_delift status metasenv subst context t1 t2 =
 let ind = !indent in
 let res = 
   try Some
    (fo_unif_w_hints true status false true(*test_eq_only*) metasenv subst
      context (false,t1) (false,t2))
    (*(unify status true(*test_eq_only*) metasenv subst
      context t1 t2 false)*)
   with UnificationFailure _ | Uncertain _ | KeepReducingThis _ -> None
 in
 indent := ind; res

and fo_unif0 during_delift status swap test_eq_only metasenv subst context (norm1,t1 as m1) (norm2,t2 as m2) =
 (*D*) inside 'F'; try let rc =  
  pp (lazy("  " ^ ppterm status ~metasenv ~subst ~context t1 ^ 
       (if swap then " ==>?== " 
        else " ==<?==" ) ^ 
      ppterm status ~metasenv ~subst ~context t2 ^ ppmetasenv status
      ~subst metasenv));
  pp (lazy("  " ^ ppterm status ~metasenv ~subst:[] ~context t1 ^
       (if swap then " ==>??== " 
        else " ==<??==" ) ^ 
      ppterm status ~metasenv ~subst:[] ~context t2 ^ ppmetasenv status
      ~subst metasenv));
  if t1 === t2 then
    metasenv, subst
(* CSC: To speed up Oliboni's stuff. Why is it necessary, anyway?
     else if
      NCicUntrusted.metas_of_term subst context t1 = [] &&
      NCicUntrusted.metas_of_term subst context t2 = []
     then
      if NCicReduction.are_convertible ~metasenv ~subst context t1 t2 then
       metasenv,subst
      else
       raise (UnificationFailure (lazy "Closed terms not convertible"))
*)
 else
   match (t1,t2) with
   | C.Appl [_], _ | _, C.Appl [_] | C.Appl [], _ | _, C.Appl [] 
   | C.Appl (C.Appl _::_), _ | _, C.Appl (C.Appl _::_) -> 
       prerr_endline "Appl [Appl _;_] or Appl [] or Appl [_] invariant";
       assert false 
   | (C.Sort (C.Type a), C.Sort (C.Type b)) when not test_eq_only ->
       let a, b = if swap then b,a else a,b in
       if NCicEnvironment.universe_leq a b then metasenv, subst
       else raise (UnificationFailure (mk_msg status metasenv subst context t1 t2))
   | (C.Sort (C.Type a), C.Sort (C.Type b)) -> 
       if NCicEnvironment.universe_eq a b then metasenv, subst
       else raise (UnificationFailure (mk_msg status metasenv subst context t1 t2))
   | (C.Sort C.Prop,C.Sort (C.Type _)) when not swap -> 
       if (not test_eq_only) then metasenv, subst
       else raise (UnificationFailure (mk_msg status metasenv subst context t1 t2))
   | (C.Sort (C.Type _), C.Sort C.Prop) when swap -> 
       if (not test_eq_only) then metasenv, subst
       else raise (UnificationFailure (mk_msg status metasenv subst context t1 t2))

   | (C.Lambda (name1,s1,t1), C.Lambda(_,s2,t2)) 
   | (C.Prod (name1,s1,t1), C.Prod(_,s2,t2)) ->
       let metasenv, subst = unify status true metasenv subst context s1 s2 swap in
       unify status test_eq_only metasenv subst ((name1, C.Decl s1)::context) t1 t2 swap
   | (C.LetIn (name1,ty1,s1,t1), C.LetIn(_,ty2,s2,t2)) ->
       let metasenv,subst=unify status test_eq_only metasenv subst context ty1 ty2 swap in
       let metasenv,subst=unify status test_eq_only metasenv subst context s1 s2 swap in
       let context = (name1, C.Def (s1,ty1))::context in
       unify status test_eq_only metasenv subst context t1 t2 swap

   | (C.Meta (n1,(s1,l1 as lc1)),C.Meta (n2,(s2,l2 as lc2))) when n1 = n2 ->
      (try 
       let l1 = NCicUtils.expand_local_context l1 in
       let l2 = NCicUtils.expand_local_context l2 in
       let metasenv, subst, to_restrict, _ =
        List.fold_right2 
         (fun t1 t2 (metasenv, subst, to_restrict, i) -> 
            try 
              let metasenv, subst = 
               unify status (*test_eq_only*) true metasenv subst context
                (NCicSubstitution.lift status s1 t1) (NCicSubstitution.lift status s2 t2)
                 swap
              in
              metasenv, subst, to_restrict, i-1  
            with UnificationFailure _ | Uncertain _ ->
              metasenv, subst, i::to_restrict, i-1)
         l1 l2 (metasenv, subst, [], List.length l1)
       in
       if to_restrict <> [] then
         let metasenv, subst, _, _ = 
           NCicMetaSubst.restrict status metasenv subst n1 to_restrict
         in
           metasenv, subst
       else metasenv, subst
      with 
       | Invalid_argument _ -> assert false
       | NCicMetaSubst.MetaSubstFailure msg ->
          try 
            let _,_,term,_ = NCicUtils.lookup_subst n1 subst in
            let term1 = NCicSubstitution.subst_meta status lc1 term in
            let term2 = NCicSubstitution.subst_meta status lc2 term in
              unify status test_eq_only metasenv subst context term1 term2 swap
          with NCicUtils.Subst_not_found _-> raise (UnificationFailure msg))

   |  NCic.Appl (NCic.Meta (i,_)::_ as l1),
      NCic.Appl (NCic.Meta (j,_)::_ as l2) when i=j ->
        (try
          List.fold_left2 
            (fun (metasenv, subst) t1 t2 ->
              unify status (*test_eq_only*) true metasenv subst context t1 
                t2 swap)
            (metasenv,subst) l1 l2
        with Invalid_argument _ -> 
          raise (UnificationFailure (mk_msg status metasenv subst context t1 t2)))
   
   | _, NCic.Meta (n, _) when is_locked n subst && not swap && not during_delift ->
       (let (metasenv, subst), i = 
          match NCicReduction.whd status ~subst context t1 with
          | NCic.Appl (NCic.Meta (i,l) as meta :: args) ->
             let metasenv, lambda_Mj =
               lambda_intros status metasenv subst context (List.length args)
                (NCicTypeChecker.typeof status ~metasenv ~subst context meta)
             in
               unify status test_eq_only metasenv subst context 
                (C.Meta (i,l)) lambda_Mj false,
               i
          | NCic.Meta (i,_) -> (metasenv, subst), i
          | _ ->
             raise (UnificationFailure (lazy "Locked term vs non
              flexible term; probably not saturated enough yet!"))
         in
          let t1 = NCicReduction.whd status ~subst context t1 in
          let j, lj = 
            match t1 with NCic.Meta (j,l) -> j, l | _ -> assert false
          in
          let metasenv, subst = 
            instantiate status test_eq_only metasenv subst context j lj t2 true
          in
          (* We need to remove the out_scope_tags to avoid propagation of
             them that triggers again the ad-hoc case *)
          let subst =
           List.map (fun (i,(tag,ctx,bo,ty)) ->
            let tag =
             List.filter
              (function `InScope | `OutScope _ -> false | _ -> true) tag
            in
              i,(tag,ctx,bo,ty)
            ) subst
          in
          (try
            let name, ctx, term, ty = NCicUtils.lookup_subst i subst in
            let term = eta_reduce status subst term in
            let subst = List.filter (fun (j,_) -> j <> i) subst in
            metasenv, ((i, (name, ctx, term, ty)) :: subst)
          with Not_found -> assert false))
   | NCic.Meta (n, _), _ when is_locked n subst && swap ->
      fo_unif0 during_delift status false test_eq_only metasenv subst context m2 m1

   | _, C.Meta (n,lc) when List.mem_assoc n subst -> 
      let _,_,term,_ = NCicUtils.lookup_subst n subst in
      let term = NCicSubstitution.subst_meta status lc term in
        fo_unif0 during_delift status swap test_eq_only metasenv subst context
         m1 (false,term)
   | C.Meta (n,_), _ when List.mem_assoc n subst -> 
      fo_unif0 during_delift status (not swap) test_eq_only metasenv subst context m2 m1

   | _, NCic.Appl (NCic.Meta (i,l)::args) when List.mem_assoc i subst ->
      let _,_,term,_ = NCicUtils.lookup_subst i subst in
      let term = NCicSubstitution.subst_meta status l term in
        fo_unif0 during_delift status swap test_eq_only metasenv subst context
         m1 (false,mk_appl status ~upto:(List.length args) term args)
   | NCic.Appl (NCic.Meta (i,_)::_), _ when List.mem_assoc i subst ->
      fo_unif0 during_delift status (not swap) test_eq_only metasenv subst context m2 m1

   | C.Meta (n,_), C.Meta (m,lc') when 
       let _,cc1,_ = NCicUtils.lookup_meta n metasenv in
       let _,cc2,_ = NCicUtils.lookup_meta m metasenv in
        (n < m && cc1 = cc2) ||
         let len1 = List.length cc1 in
         let len2 = List.length cc2 in
          len2 < len1 && cc2 = fst (HExtlib.split_nth len2 cc1) ->
      instantiate status test_eq_only metasenv subst context m lc'
        (NCicReduction.head_beta_reduce status ~subst t1) (not swap)
   | C.Meta (n,lc), C.Meta (m,lc') when
      let _,_,tyn = NCicUtils.lookup_meta n metasenv in
      let _,_,tym = NCicUtils.lookup_meta m metasenv in
      let tyn = NCicSubstitution.subst_meta status lc tyn in
      let tym = NCicSubstitution.subst_meta status lc tym in
       match tyn,tym with
          NCic.Sort NCic.Type u1, NCic.Sort NCic.Type u2 ->
           NCicEnvironment.universe_lt u1 u2
        | _,_ -> false ->
      instantiate status test_eq_only metasenv subst context m lc'
        (NCicReduction.head_beta_reduce status ~subst t1) (not swap)
   | C.Meta (n,lc), t -> 
      instantiate status test_eq_only metasenv subst context n lc 
        (NCicReduction.head_beta_reduce status ~subst t) swap
   | t, C.Meta (n,lc) -> 
      instantiate status test_eq_only metasenv subst context n lc 
       (NCicReduction.head_beta_reduce status ~subst t) (not swap)

   (* higher order unification case *)
   | NCic.Appl (NCic.Meta (i,l) as meta :: args), _ ->
       (* this easy_case handles "(? ?) =?= (f a)", same number of 
        * args, preferring the instantiation "f" over "\_.f a" for the
        * metavariable in head position. Since the arguments of the meta
        * are flexible, delift would ignore them generating a constant
        * function even in the easy case above *)
       let easy_case = 
         match t2 with
         | NCic.Appl (f :: f_args)
           when 
           List.exists (NCicMetaSubst.is_flexible status context ~subst) args ->
            let mlen = List.length args in
            let flen = List.length f_args in
            let min_len = min mlen flen in
            let mhe,margs = HExtlib.split_nth (mlen - min_len) args in
            let fhe,fargs = HExtlib.split_nth (flen - min_len) f_args in
             (try 
                Some (List.fold_left2 
                  (fun (m, s) t1 t2 -> 
                    unify status test_eq_only m s context t1 t2 swap
                  ) (metasenv,subst)
                    ((NCicUntrusted.mk_appl meta mhe)::margs)
                    ((NCicUntrusted.mk_appl f fhe)::fargs))
              with UnificationFailure _ | Uncertain _ | KeepReducing _ ->
                None) 
         | _ -> None
       in
       (match easy_case with
       | Some ms -> ms
       | None ->
           (* This case handles "(?_f ..ti..) =?= t2", abstracting every
            * non flexible ti (delift skips local context items that are
            * flexible) from t2 in two steps:
            *  1) ?_f := \..xi.. .?
            *  2) ?_f ..ti..  =?= t2 --unif_machines-->
                  ?_f[..ti..] =?= t2 --instantiate-->
                  delift [..ti..] t2 *)
           let metasenv, lambda_Mj =
             lambda_intros status metasenv subst context (List.length args)
              (NCicTypeChecker.typeof status ~metasenv ~subst context meta)
           in
           let metasenv, subst = 
             unify status test_eq_only metasenv subst context 
               (C.Meta (i,l)) lambda_Mj swap
           in
           let metasenv, subst = 
             unify status test_eq_only metasenv subst context t1 t2 swap
           in
           (try
             let name, ctx, term, ty = NCicUtils.lookup_subst i subst in
             let term = eta_reduce status subst term in
             let subst = List.filter (fun (j,_) -> j <> i) subst in
             metasenv, ((i, (name, ctx, term, ty)) :: subst)
           with Not_found -> assert false))

   | _, NCic.Appl (NCic.Meta (_,_) :: _) ->
     fo_unif0 during_delift status (not swap) test_eq_only metasenv subst context m2 m1

   | (C.Appl (hd1::tl1), C.Appl (hd2::tl2)) ->
       let metasenv,subst =
        fo_unif0 during_delift status swap test_eq_only metasenv subst context
         (false,hd1) (false,hd2) in
       let relevance =
         match hd1 with
         | C.Const r -> NCicEnvironment.get_relevance status r
         | _ -> [] in
       let metasenv, subst, _ = 
         try
           List.fold_left2 
             (fun (metasenv, subst, relevance) t1 t2 ->
                let b, relevance = 
                  match relevance with b::tl -> b,tl | _ -> true, [] in
                let metasenv, subst = 
                  try unify status test_eq_only metasenv subst context t1 t2
                        swap
                  with UnificationFailure _ | Uncertain _ when not b ->
                    metasenv, subst
                in
                  metasenv, subst, relevance)
             (metasenv, subst, relevance) tl1 tl2
         with
            Invalid_argument _ -> 
             raise (Uncertain (mk_msg status metasenv subst context t1 t2))
          | KeepReducing _ | KeepReducingThis _ -> assert false
       in 
         metasenv, subst

   | (C.Match (Ref.Ref (_,Ref.Ind (_,tyno,_)) as ref1,outtype1,term1,pl1),
      C.Match (ref2,outtype2,term2,pl2)) when Ref.eq ref1 ref2 ->
       let _,_,itl,_,_ = NCicEnvironment.get_checked_indtys status ref1 in
       let _,_,ty,_ = List.nth itl tyno in
       let rec remove_prods ~subst context ty = 
         let ty = NCicReduction.whd status ~subst context ty in
         match ty with
         | C.Sort _ -> ty
         | C.Prod (name,so,ta) -> 
               remove_prods ~subst ((name,(C.Decl so))::context) ta
         | _ -> assert false
       in
       let is_prop = 
         match remove_prods ~subst [] ty with
         | C.Sort C.Prop -> true
         | _ -> false 
       in
       (* if not (Ref.eq ref1 ref2) then 
         raise (Uncertain (mk_msg status metasenv subst context t1 t2))
       else*)
         let metasenv, subst = 
          unify status test_eq_only metasenv subst context outtype1 outtype2 swap in
         let metasenv, subst = 
           try unify status test_eq_only metasenv subst context term1 term2 swap
           with UnificationFailure _ | Uncertain _ when is_prop -> 
             metasenv, subst
         in
         (try
          List.fold_left2 
           (fun (metasenv,subst) t1 t2 -> 
              unify status test_eq_only metasenv subst context t1 t2 swap)
           (metasenv, subst) pl1 pl2
         with Invalid_argument _ -> assert false)
   | (C.Implicit _, _) | (_, C.Implicit _) -> assert false
   | _ when norm1 && norm2 ->
       if (could_reduce status ~subst context t1 || could_reduce status ~subst context t2) then
        raise (Uncertain (mk_msg status metasenv subst context t1 t2))
       else
        raise (UnificationFailure (mk_msg status metasenv subst context t1 t2))
   | _ -> raise (KeepReducing (mk_msg status metasenv subst context t1 t2))
 (*D*)  in outside None; rc with exn -> outside (Some exn); raise exn 

and try_hints status swap test_eq_only metasenv subst context (_,t1 as mt1) (_,t2 as mt2) (* exc*) =
  if NCicUntrusted.metas_of_term status subst context t1 = [] &&
     NCicUntrusted.metas_of_term status subst context t2 = [] 
  then None 
  else begin
(*D*) inside 'H'; try let rc =  
 pp(lazy ("\nProblema:\n" ^
    ppterm status ~metasenv ~subst ~context t1 ^ " =?= " ^
    ppterm status ~metasenv ~subst ~context t2));
  let candidates = 
    NCicUnifHint.look_for_hint status metasenv subst context t1 t2
  in
  let rec cand_iter = function
    | [] -> None (* raise exc *)
    | (metasenv,(c1,c2),premises)::tl -> 
        pp (lazy ("\nProvo il candidato:\n" ^ 
          String.concat "\n"
            (List.map 
              (fun (a,b) ->
               ppterm status ~metasenv ~subst ~context a ^  " =?= " ^
               ppterm status ~metasenv ~subst ~context b) premises) ^
          "\n-------------------------------------------\n"^
          ppterm status ~metasenv ~subst ~context c1 ^  " = " ^
          ppterm status ~metasenv ~subst ~context c2));
        try 
(*D*) inside 'K'; try let rc =  
          let metasenv,subst = 
           fo_unif false status swap test_eq_only metasenv subst context mt1 (false,c1) in
          let metasenv,subst = 
           fo_unif false status swap test_eq_only metasenv subst context (false,c2) mt2 in
          let metasenv,subst = 
            List.fold_left 
              (fun (metasenv, subst) (x,y) ->
                 unify status test_eq_only metasenv subst context x y false)
              (metasenv, subst) (List.rev premises)
          in
          pp(lazy("FUNZIONA!"));
          Some (metasenv, subst)
 (*D*)  in outside None; rc with exn -> outside (Some exn); raise exn 
        with
         KeepReducing _ | UnificationFailure _ | Uncertain _ -> cand_iter tl
       | KeepReducingThis _ -> assert false
  in
    cand_iter candidates
 (*D*)  in outside None; rc with exn -> outside (Some exn); raise exn 
  end

and fo_unif during_delift status swap test_eq_only metasenv subst context (norm1,t1 as nt1) (norm2,t2 as nt2)=
 try fo_unif0 during_delift status swap test_eq_only metasenv subst context nt1 nt2
 with
  UnificationFailure _ | Uncertain _ when not norm1 || not norm2 ->
   raise (KeepReducing (mk_msg status metasenv subst context t1 t2))

and unify status test_eq_only metasenv subst context t1 t2 swap =
 (*D*) inside 'U'; try let rc =
    let fo_unif_heads_and_cont_or_unwind_and_hints 
      test_eq_only metasenv subst m1 m2 cont hm1 hm2
     =
      let ms, continuation = 
        (* calling the continuation inside the outermost try is an option
           and makes unification stronger, but looks not frequent to me
           that heads unify but not the arguments and that an hints can fix 
           that *)
        try fo_unif false status swap test_eq_only metasenv subst context m1 m2, cont
        with 
        | UnificationFailure _ 
        | KeepReducing _ | Uncertain _ as exn ->
           let (t1,norm1),(t2,norm2) = hm1, hm2 in
           match 
             try_hints status swap test_eq_only metasenv subst context
              (norm1,NCicReduction.unwind status t1) (norm2,NCicReduction.unwind status t2)
           with
            | Some x -> x, fun x -> x
            | None -> 
                match exn with 
                | KeepReducing msg -> raise (KeepReducingThis (msg,hm1,hm2))
                | UnificationFailure _ | Uncertain _ as exn -> raise exn
                | _ -> assert false
      in
        continuation ms
    in
    let height_of = function
     | NCic.Const (Ref.Ref (_,Ref.Def h)) 
     | NCic.Const (Ref.Ref (_,Ref.Fix (_,_,h))) 
     | NCic.Appl(NCic.Const(Ref.Ref(_,Ref.Def h))::_) 
     | NCic.Appl(NCic.Const(Ref.Ref(_,Ref.Fix (_,_,h)))::_) -> h
     | _ -> 0
    in
    let small_delta_step ~subst  
      ((_,_,t1,_ as m1, norm1) as x1) ((_,_,t2,_ as m2, norm2) as x2)
    =
     assert (not (norm1 && norm2));
     if norm1 then
      x1,NCicReduction.reduce_machine status ~delta:0 ~subst context m2
     else if norm2 then
      NCicReduction.reduce_machine status ~delta:0 ~subst context m1,x2
     else 
      let h1 = height_of t1 in 
      let h2 = height_of t2 in
      let delta = if h1 = h2 then max 0 (h1 -1) else min h1 h2 in
      NCicReduction.reduce_machine status ~delta ~subst context m1,
      NCicReduction.reduce_machine status ~delta ~subst context m2
    in
    let rec unif_machines metasenv subst = 
      function
      | ((k1,e1,t1,s1),norm1 as m1),((k2,e2,t2,s2),norm2 as m2) ->
     (*D*) inside 'M'; try let rc = 
         pp (lazy("UM: " ^
           ppterm status ~metasenv ~subst ~context 
             (NCicReduction.unwind status (k1,e1,t1,s1)) ^
           " === " ^ 
           ppterm status ~metasenv ~subst ~context 
             (NCicReduction.unwind status (k2,e2,t2,s2))));
         pp (lazy (string_of_bool norm1 ^ " ?? " ^ string_of_bool norm2));
          let relevance =
            match t1 with
            | C.Const r -> NCicEnvironment.get_relevance status r
            | _ -> [] in
          let unif_from_stack (metasenv, subst) (t1, t2, b) =
              try
                let t1 = NCicReduction.from_stack ~delta:max_int t1 in
                let t2 = NCicReduction.from_stack ~delta:max_int t2 in
                unif_machines metasenv subst (put_in_whd status subst context t1 t2)
              with UnificationFailure _ | Uncertain _ when not b ->
                metasenv, subst
          in
          let rec check_stack l1 l2 r todo =
            match l1,l2,r with
            | x1::tl1, x2::tl2, r::tr-> check_stack tl1 tl2 tr ((x1,x2,r)::todo)
            | x1::tl1, x2::tl2, []-> check_stack tl1 tl2 [] ((x1,x2,true)::todo)
            | l1, l2, _ ->
               NCicReduction.unwind status (k1,e1,t1,List.rev l1),
                NCicReduction.unwind status (k2,e2,t2,List.rev l2),
                todo
          in
          let check_stack l1 l2 r =
            match t1, t2 with
            | NCic.Meta _, _ | _, NCic.Meta _ ->
                (NCicReduction.unwind status (k1,e1,t1,s1)),
                (NCicReduction.unwind status (k2,e2,t2,s2)),[]
            | _ -> check_stack l1 l2 r []
          in
        let hh1,hh2,todo =
          check_stack (List.rev s1) (List.rev s2) (List.rev relevance) in
        try
          fo_unif_heads_and_cont_or_unwind_and_hints
            test_eq_only metasenv subst (norm1,hh1) (norm2,hh2) 
            (fun ms -> List.fold_left unif_from_stack ms todo)
            m1 m2
        with
         | KeepReducing _ -> assert false
         | KeepReducingThis _ ->
            assert (not (norm1 && norm2));
            unif_machines metasenv subst (small_delta_step ~subst m1 m2)
         | UnificationFailure _ | Uncertain _ when (not (norm1 && norm2))
           -> unif_machines metasenv subst (small_delta_step ~subst m1 m2)
         | UnificationFailure msg
           when could_reduce status ~subst context (NCicReduction.unwind status (fst m1))
             || could_reduce status ~subst context (NCicReduction.unwind status (fst m2))
           -> raise (Uncertain msg)
      (*D*)  in outside None; rc with exn -> outside (Some exn); raise exn 
     in
     try fo_unif_w_hints false status swap test_eq_only metasenv subst context (false,t1) (false,t2)
     with
      | KeepReducingThis (msg,tm1,tm2) ->
         (try 
           unif_machines metasenv subst (tm1,tm2)
          with 
          | UnificationFailure _ -> raise (UnificationFailure msg)
          | Uncertain _ -> raise (Uncertain msg)
          | KeepReducing _ -> assert false)
      | KeepReducing _ -> assert false

 (*D*)  in outside None; rc with KeepReducing _ -> assert false | exn -> outside (Some exn); raise exn 

and delift_type_wrt_terms status metasenv subst context t args =
  let lc = List.rev args @ mk_irl (List.length context) (List.length args+1) in
  let (metasenv, subst), t =
   try
    NCicMetaSubst.delift status ~unify:(unify_for_delift status)
      metasenv subst context (-1) (0,NCic.Ctx lc) t
   with
      NCicMetaSubst.MetaSubstFailure _
    | NCicMetaSubst.Uncertain _ -> (metasenv, subst), t
  in
   metasenv, subst, t
;;


let unify status ?(test_eq_only=false) ?(swap=false) metasenv subst context t1 t2= 
  indent := "";      
  unify status test_eq_only metasenv subst context t1 t2 swap;;

let fix_sorts status m s =
  fix status m s true false (UnificationFailure (lazy "no sup"))
;;
