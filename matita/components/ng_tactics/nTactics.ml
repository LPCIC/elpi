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

open Printf

let debug = false
let debug_print s = if debug then prerr_endline (Lazy.force s) else ()

open Continuationals.Stack
open NTacStatus
module Ast = NotationPt

let id_tac status = status ;;
let print_tac print_status message status = 
  if print_status then pp_tac_status status;
  prerr_endline message; 
  status
;;

let dot_tac status =
  let gstatus = 
    match status#stack with
    | [] -> assert false
    | ([], _, [], _) :: _ as stack ->
        (* backward compatibility: do-nothing-dot *)
        stack
    | (g, t, k, tag) :: s ->
        match filter_open g, k with
        | loc :: loc_tl, _ -> 
             (([ loc ], t, loc_tl @+ k, tag) :: s) 
        | [], loc :: k ->
            assert (is_open loc);
            (([ loc ], t, k, tag) :: s)
        | _ -> fail (lazy "can't use \".\" here")
  in
   status#set_stack gstatus
;;

let branch_tac ?(force=false) status =
  let gstatus = 
    match status#stack with
    | [] -> assert false
    | (g, t, k, tag) :: s ->
          match init_pos g with (* TODO *)
          | [] -> fail (lazy "empty goals")
	  | [_] when (not force) -> fail (lazy "too few goals to branch")
          | loc :: loc_tl ->
               ([ loc ], [], [], `BranchTag) :: (loc_tl, t, k, tag) :: s
  in
   status#set_stack gstatus
;;

let shift_tac status =
  let gstatus = 
    match status#stack with
    | (g, t, k, `BranchTag) :: (g', t', k', tag) :: s ->
          (match g' with
          | [] -> fail (lazy "no more goals to shift")
          | loc :: loc_tl ->
                (([ loc ], t @+ filter_open g @+ k, [],`BranchTag)
                :: (loc_tl, t', k', tag) :: s))
     | _ -> fail (lazy "can't shift goals here")
  in
   status#set_stack gstatus
;;

let pos_tac i_s status =
  let gstatus = 
    match status#stack with
    | [] -> assert false
    | ([ loc ], t, [],`BranchTag) :: (g', t', k', tag) :: s
      when is_fresh loc ->
        let l_js = List.filter (fun (i, _) -> List.mem i i_s) ([loc] @+ g') in
          ((l_js, t , [],`BranchTag)
           :: (([ loc ] @+ g') @- l_js, t', k', tag) :: s)
    | _ -> fail (lazy "can't use relative positioning here")
  in
   status#set_stack gstatus
;;

let case_tac lab status =
  let gstatus = 
    match status#stack with
    | [] -> assert false
    | ([ loc ], t, [],`BranchTag) :: (g', t', k', tag) :: s
      when is_fresh loc ->
        let l_js =
          List.filter 
           (fun curloc -> 
              let _,_,metasenv,_,_ = status#obj in
              match NCicUtils.lookup_meta (goal_of_loc curloc) metasenv with
                  attrs,_,_ when List.mem (`Name lab) attrs -> true
                | _ -> false) ([loc] @+ g') in
          ((l_js, t , [],`BranchTag)
           :: (([ loc ] @+ g') @- l_js, t', k', tag) :: s)
    | _ -> fail (lazy "can't use relative positioning here")
  in
   status#set_stack gstatus
;;

let wildcard_tac status =
  let gstatus = 
    match status#stack with
    | [] -> assert false
    | ([ loc ] , t, [], `BranchTag) :: (g', t', k', tag) :: s
       when is_fresh loc ->
            (([loc] @+ g', t, [], `BranchTag) :: ([], t', k', tag) :: s)
    | _ -> fail (lazy "can't use wildcard here")
  in
   status#set_stack gstatus
;;

let merge_tac status =
  let gstatus = 
    match status#stack with
    | [] -> assert false
    | (g, t, k,`BranchTag) :: (g', t', k', tag) :: s ->
        ((t @+ filter_open g @+ g' @+ k, t', k', tag) :: s)
    | _ -> fail (lazy "can't merge goals here")
  in
   status#set_stack gstatus
;;
      
let focus_tac gs status =
  let gstatus = 
    match status#stack with
    | [] -> assert false
    | s -> assert(gs <> []);
          let stack_locs =
            let add_l acc _ _ l = if is_open l then l :: acc else acc in
            fold ~env:add_l ~cont:add_l ~todo:add_l [] s
          in
          List.iter
            (fun g ->
              if not (List.exists (fun l -> goal_of_loc l = g) stack_locs) then
                fail (lazy (sprintf "goal %d not found (or closed)" g)))
            gs;
          (zero_pos gs, [], [], `FocusTag) :: deep_close gs s
  in
   status#set_stack gstatus
;;

let unfocus_tac status =
  let gstatus = 
    match status#stack with
    | [] -> assert false
    | (g, [], [], `FocusTag) :: s when filter_open g = [] -> s
    | _ as s -> fail (lazy ("can't unfocus, some goals are still open:\n"^
      Continuationals.Stack.pp s))
  in
   status#set_stack gstatus
;;

let skip_tac status =
  let gstatus = 
    match status#stack with
    | [] -> assert false
    | (gl, t, k, tag) :: s -> 
        let gl = List.map switch_of_loc gl in
        if List.exists (function Open _ -> true | Closed _ -> false) gl then 
          fail (lazy "cannot skip an open goal")
        else 
          ([],t,k,tag) :: s
  in
   status#set_stack gstatus
;;

let block_tac l status =
  List.fold_left (fun status tac -> tac status) status l
;;


let compare_statuses ~past ~present =
 let _,_,past,_,_ = past#obj in 
 let _,_,present,_,_ = present#obj in 
 List.map fst (List.filter (fun (i,_) -> not(List.mem_assoc i past)) present),
 List.map fst (List.filter (fun (i,_) -> not (List.mem_assoc i present)) past)
;;



(* Exec and distribute_tac form a retraction pair:
    1) exec (distribute_tac low_tac) (s,i) = low_tac (s,i)
    2) tac [s]::G = G1::...::Gn::G' && G' is G with some goals closed =>
         distribute_tac (exec tac) [s]::G = (G1@...Gn)::G'
    3) tac G = distribute_tac (exec tac) G if  
       tac = distribute_tac lowtac
    4) atomic_tac t === distribute_tac (exec t)

   Note that executing an high tactic on a set of goals may be stronger
   than executing the same tactic on those goals, but once at a time
   (e.g. the tactic could perform a global analysis of the set of goals)
*)

(* CSC: potential bug here: the new methods still use the instance variables
   of the old status and not the instance variables of the new one *)
let change_stack_type (status : 'a #NTacStatus.status) (stack: 'b) : 'b NTacStatus.status =
 let o =
  object
   inherit ['b] NTacStatus.status status#obj stack
   method ppterm = status#ppterm
   method ppcontext = status#ppcontext
   method ppsubst = status#ppsubst
   method ppobj = status#ppobj
   method ppmetasenv = status#ppmetasenv
  end
 in
  o#set_pstatus status
;;

let exec tac (low_status : #lowtac_status) g =
  let stack = [ [0,Open g], [], [], `NoTag ] in
  let status = change_stack_type low_status stack in
  let status = tac status in
   (low_status#set_pstatus status)#set_obj status#obj
;;

let distribute_tac tac (status : #tac_status) =
  match status#stack with
  | [] -> assert false
  | (g, t, k, tag) :: s ->
      debug_print (lazy ("context length " ^string_of_int (List.length g)));
      let rec aux s go gc =
        function
        | [] -> 
            debug_print (lazy "no selected goals");
            s, go, gc
        | loc :: loc_tl ->
            debug_print (lazy "inner eval tactical");
            let s, go, gc =
              if List.exists ((=) (goal_of_loc loc)) gc then
                s, go, gc
              else
                match switch_of_loc loc with
                | Closed _ -> fail (lazy "cannot apply to a Closed goal")
                | Open n -> 
                   let sn = tac s n in
                   let go', gc' = compare_statuses ~past:s ~present:sn in
                   sn, ((go @+ [n]) @- gc') @+ go', gc @+ gc'
            in
            aux s go gc loc_tl
      in
      let s0 = change_stack_type status () in
      let s0, go0, gc0 = s0, [], [] in
      let sn, gon, gcn = aux s0 go0 gc0 g in
      debug_print (lazy ("opened: "
        ^ String.concat " " (List.map string_of_int gon)));
      debug_print (lazy ("closed: "
        ^ String.concat " " (List.map string_of_int gcn)));
      let stack =
        (zero_pos gon, t @~- gcn, k @~- gcn, tag) :: deep_close gcn s
      in
       ((status#set_stack stack)#set_obj(sn:>lowtac_status)#obj)#set_pstatus sn
;;

let atomic_tac htac: #tac_status as 'a -> 'a = distribute_tac (exec htac) ;;

let repeat_tac t s = 
  let rec repeat t (status : #tac_status as 'a) : 'a = 
    try repeat t (t status)
    with NTacStatus.Error _ -> status
  in
    atomic_tac (repeat t) s
;;


let try_tac tac status =
 let try_tac status =
  try
    tac status
  with NTacStatus.Error _ ->
    status
 in
  atomic_tac try_tac status
;;

let first_tac tacl status =
  let res = 
   HExtlib.list_findopt
    (fun tac _ -> try Some (tac status) with NTacStatus.Error _ -> None) tacl
  in
    match res with
      | None -> fail (lazy "No tactics left")
      | Some x -> x
;;

let exact_tac t : 's tactic = distribute_tac (fun status goal ->
 instantiate_with_ast status goal t)
;;

let assumption_tac status = distribute_tac (fun status goal ->
  let gty = get_goalty status goal in
  let context = ctx_of gty in
  let htac = 
   first_tac
    (List.map (fun (name,_) -> exact_tac ("",0,(Ast.Ident (name,None))))
      context)
  in
    exec htac status goal) status
;;

let find_in_context name context =
  let rec aux acc = function
    | [] -> raise Not_found
    | (hd,_) :: tl when hd = name -> acc
    | _ :: tl ->  aux (acc + 1) tl
  in
  aux 1 context
;;

let clear_tac names =
 if names = [] then id_tac
 else
  distribute_tac (fun status goal ->
   let goalty = get_goalty status goal in
   let js =
     List.map 
     (fun name -> 
        try find_in_context name (ctx_of goalty)
        with Not_found -> 
          fail (lazy ("hypothesis '" ^ name ^ "' not found"))) 
     names
   in
   let n,h,metasenv,subst,o = status#obj in
   let metasenv,subst,_,_ = NCicMetaSubst.restrict status metasenv subst goal js in
    status#set_obj (n,h,metasenv,subst,o))
;;

let generalize0_tac args =
 if args = [] then id_tac
 else exact_tac ("",0,Ast.Appl (Ast.Implicit `JustOne :: args))
;;

let select0_tac ~where ~job  =
 let found, postprocess = 
   match job with
   | `Substexpand argsno -> mk_in_scope, mk_out_scope argsno
   | `Collect l -> (fun s t -> l := t::!l; mk_in_scope s t), mk_out_scope 1
   | `ChangeWith f -> f,(fun s t -> s, t)
 in
 distribute_tac (fun status goal ->
   let wanted,hyps,where =
    GrafiteDisambiguate.disambiguate_npattern status where in
   let goalty = get_goalty status goal in
   let path = 
     match where with None -> NCic.Implicit `Term | Some where -> where 
   in
   let status, newgoalctx =
      List.fold_right
       (fun (name,d as entry) (status,ctx) ->
         try
          let path = List.assoc name hyps in
           match d with
              NCic.Decl ty ->
               let status,ty =
                select_term status ~found ~postprocess (mk_cic_term ctx ty)
                 (wanted,path) in
               let status,ty = term_of_cic_term status ty ctx in
                status,(name,NCic.Decl ty)::ctx
            | NCic.Def (bo,ty) ->
               let status,bo =
                select_term status ~found ~postprocess (mk_cic_term ctx bo)
                 (wanted,path) in
               let status,bo = term_of_cic_term status bo ctx in
                status,(name,NCic.Def (bo,ty))::ctx
         with
          Not_found -> status, entry::ctx
       ) (ctx_of goalty) (status,[])
   in
   let status, newgoalty = 
     select_term status ~found ~postprocess goalty (wanted,path) in
   (* WARNING: the next two lines simply change the context of newgoalty
      from the old to the new one. Otherwise mk_meta will do that herself,
      calling relocate that calls delift. However, newgoalty is now
      ?[out_scope] and thus the delift would trigger the special unification
      case, which is wrong now :-( *)
   let status,newgoalty = term_of_cic_term status newgoalty (ctx_of goalty) in
   let newgoalty = mk_cic_term newgoalctx newgoalty in

   let status, instance = 
     mk_meta status newgoalctx (`Decl newgoalty) `IsTerm
   in
   instantiate ~refine:false status goal instance) 
;;

let select_tac ~where:((txt,txtlen,(wanted,hyps,path)) as where) ~job
 move_down_hyps
=
 if not move_down_hyps then
  select0_tac ~where ~job
 else
  let path = 
   List.fold_left
    (fun path (name,ty) ->
      NotationPt.Binder (`Forall, (NotationPt.Ident (name,None),Some ty),path))
    (match path with Some x -> x | None -> NotationPt.UserInput) (List.rev hyps)
  in
   block_tac [ 
     generalize0_tac (List.map (fun (name,_) -> Ast.Ident (name,None)) hyps);
     select0_tac ~where:(txt,txtlen,(wanted,[],Some path)) ~job;
     clear_tac (List.map fst hyps) ]
;;

let generalize_tac ~where = 
 let l = ref [] in
 block_tac [ 
   select_tac ~where ~job:(`Collect l) true; 
   (fun s -> distribute_tac (fun status goal ->
      let goalty = get_goalty status goal in
      let status,canon,rest =
       match !l with
          [] ->
           (match where with
               _,_,(None,_,_)  -> fail (lazy "No term to generalize")
             | txt,txtlen,(Some what,_,_) ->
                let status, what =
                 disambiguate status (ctx_of goalty) (txt,txtlen,what) `XTNone
                in
                 status,what,[]
           )
        | he::tl -> status,he,tl in
      let status = 
       List.fold_left 
         (fun s t -> unify s (ctx_of goalty) canon t) status rest in
      let status, canon = term_of_cic_term status canon (ctx_of goalty) in
      instantiate status goal 
       (mk_cic_term (ctx_of goalty) (NCic.Appl [NCic.Implicit `Term ; canon ]))
   ) s) ]
;;

let cut_tac t = 
 atomic_tac (block_tac [ 
  exact_tac ("",0, Ast.Appl [Ast.Implicit `JustOne; Ast.Implicit `JustOne]);
  branch_tac;
   pos_tac [3]; exact_tac t;
   shift_tac; pos_tac [2]; skip_tac;
  merge_tac ])
;;

let lapply_tac (s,n,t) = 
 exact_tac (s,n, Ast.Appl [Ast.Implicit `JustOne; t])
;;

let reduce_tac ~reduction ~where =
  let change status t = 
    match reduction with
    | `Normalize perform_delta ->
        normalize status
         ?delta:(if perform_delta then None else Some max_int) (ctx_of t) t
    | `Whd perform_delta -> 
        whd status
         ?delta:(if perform_delta then None else Some max_int) (ctx_of t) t
  in
  select_tac ~where ~job:(`ChangeWith change) false
;;

let change_tac ~where ~with_what =
  let change status t = 
(* FG: `XTSort could be used when we change the whole goal *)    
    let status, ww = disambiguate status (ctx_of t) with_what `XTNone in
    let status = unify status (ctx_of t) t ww in
    status, ww
  in
  select_tac ~where ~job:(`ChangeWith change) false
;;

let letin_tac ~where ~what:(_,_,w) name =
 block_tac [
  select_tac ~where ~job:(`Substexpand 1) true;
  exact_tac
   ("",0,Ast.LetIn((Ast.Ident (name,None),None),w,Ast.Implicit `JustOne));
 ]
;;

let apply_tac (s,n,t) = 
  let t = Ast.Appl [t; Ast.Implicit `Vector] in
  exact_tac (s,n,t)
;;

type indtyinfo = {
        rightno: int;
        leftno: int;
        consno: int;
        reference: NReference.reference;
 }
;;

let ref_of_indtyinfo iti = iti.reference;;

let analyze_indty_tac ~what indtyref =
 distribute_tac (fun (status as orig_status) goal ->
  let goalty = get_goalty status goal in
  let status, what = disambiguate status (ctx_of goalty) what `XTInd in
  let status, ty_what = typeof status (ctx_of what) what in 
  let status, (r,consno,lefts,rights) = analyse_indty status ty_what in
  let leftno = List.length lefts in
  let rightno = List.length rights in
  indtyref := Some { 
    rightno = rightno; leftno = leftno; consno = consno; reference = r;
  };
  exec id_tac orig_status goal)
;;

let sort_of_goal_tac sortref = distribute_tac (fun status goal ->
  let goalty = get_goalty status goal in
  let status,sort = typeof status (ctx_of goalty) goalty in
  let status, sort = fix_sorts status sort in
  let ctx = ctx_of goalty in
  let status, sort = whd status (ctx_of sort) sort in
  let status, sort = term_of_cic_term status sort ctx in
   sortref := sort;
   status)
;;

let elim_tac ~what:(txt,len,what) ~where = 
  let what = txt, len, Ast.Appl [what; Ast.Implicit `Vector] in
  let indtyinfo = ref None in
  let sort = ref (NCic.Rel 1) in
  atomic_tac (block_tac [
    analyze_indty_tac ~what indtyinfo;    
    (fun s -> select_tac 
      ~where ~job:(`Substexpand ((HExtlib.unopt !indtyinfo).rightno+1)) true s);
    sort_of_goal_tac sort;
    (fun status ->
     let ity = HExtlib.unopt !indtyinfo in
     let NReference.Ref (uri, _) = ity.reference in
     let name = 
       NUri.name_of_uri uri ^ "_" ^
        snd (NCicElim.ast_of_sort 
          (match !sort with NCic.Sort x -> x | _ -> assert false))
     in
     let eliminator = 
       let _,_,w = what in
       Ast.Appl [ Ast.Ident (name,None) ; Ast.Implicit `Vector ; w ]
     in
     exact_tac ("",0,eliminator) status) ]) 
;;

let rewrite_tac ~dir ~what:(_,_,what) ~where status =
 let sortref = ref (NCic.Rel 1) in
 let status = sort_of_goal_tac sortref status in
 let suffix = "_" ^ snd (NCicElim.ast_of_sort 
   (match !sortref with NCic.Sort x -> x | _ -> assert false))
 in
 let name =
  match dir with
     `LeftToRight -> "eq" ^ suffix ^ "_r"
   | `RightToLeft -> "eq" ^ suffix
 in
 let what = Ast.Appl [what; Ast.Implicit `Vector] in
  block_tac
   [ select_tac ~where ~job:(`Substexpand 2) true;
     exact_tac
      ("",0,
       Ast.Appl(Ast.Ident(name,None)::HExtlib.mk_list (Ast.Implicit `JustOne) 5@
        [what]))] status
;;

let intro_tac name =
 block_tac
  [ exact_tac
     ("",0,(Ast.Binder (`Lambda,
      (Ast.Ident (name,None),None),Ast.Implicit `JustOne)));
    if name = "_" then clear_tac [name] else id_tac ]
;;

let name_counter = ref 0;;
let intros_tac ?names_ref names s =
  let names_ref, prefix = 
    match names_ref with | None -> ref [], "__" | Some r -> r, "H" 
  in
  if names = [] then
   repeat_tac 
     (fun s ->
        incr name_counter;
        (* TODO: generate better names *)
        let name = prefix ^ string_of_int !name_counter in
        let s = intro_tac name s in 
        names_ref := !names_ref @ [name];
        s)
     s
   else
     block_tac (List.map intro_tac names) s
;;

let cases ~what status goal =
 let gty = get_goalty status goal in
 let status, what = disambiguate status (ctx_of gty) what `XTInd in
 let status, ty = typeof status (ctx_of what) what in
 let status, (ref, consno, _, _) = analyse_indty status ty in
 let status, what = term_of_cic_term status what (ctx_of gty) in
 let t =
  NCic.Match (ref,NCic.Implicit `Term, what,
    HExtlib.mk_list (NCic.Implicit `Term) consno)
 in 
 instantiate status goal (mk_cic_term (ctx_of gty) t)
;;

let cases_tac ~what:(txt,len,what) ~where = 
  let what = txt, len, Ast.Appl [what; Ast.Implicit `Vector] in
  let indtyinfo = ref None in
  atomic_tac 
   (block_tac [
      analyze_indty_tac ~what indtyinfo;
      (fun s -> select_tac 
       ~where ~job:(`Substexpand ((HExtlib.unopt !indtyinfo).rightno+1))true s);
      distribute_tac (cases ~what) ])
;;

let case1_tac name =
 let name = if name = "_" then "_clearme" else name in
 block_tac [ intro_tac name; 
             cases_tac 
              ~where:("",0,(None,[],None)) 
              ~what:("",0,Ast.Ident (name,None));
             if name = "_clearme" then clear_tac ["_clearme"] else id_tac ]
;;

let constructor_tac ?(num=1) ~args = distribute_tac (fun status goal ->
  let gty = get_goalty status goal in
  let status, (r,consno,_,_) = analyse_indty status gty in
  if num < 1 || num > consno then fail (lazy "Non existant constructor");
  let ref = NReference.mk_constructor num r in
  let t = 
    if args = [] then Ast.NRef ref else
    Ast.Appl (HExtlib.list_concat ~sep:[Ast.Implicit `Vector]
      ([Ast.NRef ref] :: List.map (fun _,_,x -> [x]) args))
  in
  exec (apply_tac ("",0,t)) status goal)
;;

let assert0_tac (hyps,concl) = distribute_tac (fun status goal ->
 let gty = get_goalty status goal in
 let eq status ctx t1 t2 =
  let status,t1 = disambiguate status ctx t1 `XTSort in
  let status,t1 = apply_subst status ctx t1 in
  let status,t1 = term_of_cic_term status t1 ctx in
  let t2 = mk_cic_term ctx t2 in
  let status,t2 = apply_subst status ctx t2 in
  let status,t2 = term_of_cic_term status t2 ctx in
  prerr_endline ("COMPARING: " ^ status#ppterm ~subst:[] ~metasenv:[] ~context:ctx t1 ^ " vs " ^ status#ppterm ~subst:[] ~metasenv:[] ~context:ctx t2);
  assert (t1=t2);
  status
 in
 let status,gty' = term_of_cic_term status gty (ctx_of gty) in
 let status = eq status (ctx_of gty) concl gty' in
 let status,_ =
  List.fold_right2
   (fun (id1,e1) ((id2,e2) as item) (status,ctx) ->
     assert (id1=id2 || (prerr_endline (id1 ^ " vs " ^ id2); false));
     match e1,e2 with
        `Decl t1, NCic.Decl t2 ->
          let status = eq status ctx t1 t2 in
          status,item::ctx
      | `Def (b1,t1), NCic.Def (b2,t2) ->
          let status = eq status ctx t1 t2 in
          let status = eq status ctx b1 b2 in
          status,item::ctx
      | _ -> assert false
   ) hyps (ctx_of gty) (status,[])
 in
  exec id_tac status goal)
;;

let assert_tac seqs status =
 match status#stack with
  | [] -> assert false
  | (g,_,_,_) :: s ->
     assert (List.length g = List.length seqs);
     (match seqs with
         [] -> id_tac
       | [seq] -> assert0_tac seq
       | _ ->
         block_tac
          ((branch_tac ~force:false)::
          HExtlib.list_concat ~sep:[shift_tac]
            (List.map (fun seq -> [assert0_tac seq]) seqs)@
          [merge_tac])
     ) status
;;

let inversion_tac ~what:(txt,len,what) ~where = 
  let what = txt, len, Ast.Appl [what; Ast.Implicit `Vector] in
  let indtyinfo = ref None in
  let sort = ref (NCic.Rel 1) in
  atomic_tac (block_tac [
    analyze_indty_tac ~what indtyinfo;    
    (fun s -> select_tac 
      ~where ~job:(`Substexpand ((HExtlib.unopt !indtyinfo).rightno+1)) true s);
    sort_of_goal_tac sort;
    (fun status ->
     let ity = HExtlib.unopt !indtyinfo in
     let NReference.Ref (uri, _) = ity.reference in
     let name = 
       NUri.name_of_uri uri ^ "_inv_" ^
        snd (NCicElim.ast_of_sort 
          (match !sort with NCic.Sort x -> x | _ -> assert false))
     in
     let eliminator = 
       let _,_,w = what in
       Ast.Appl [ Ast.Ident (name,None) ; Ast.Implicit `Vector ; w ; Ast.Implicit `Vector]
     in
     exact_tac ("",0,eliminator) status) ]) 
;;
