(* Copyright (C) 2002, HELM Team.
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

(* $Id: destructTactic.ml 9774 2009-05-15 19:37:08Z sacerdot $ *)

open NTacStatus
open Continuationals.Stack

let debug = false
let pp = 
  if debug then (fun x -> prerr_endline (Lazy.force x)) else (fun _ -> ())

let fresh_name =
 let i = ref 0 in
 function () ->
  incr i;
  "z" ^ string_of_int !i
;;

let mk_id id =
 let id = if id = "_" then fresh_name () else id in
  NotationPt.Ident (id,None)
;;

let mk_sym s = NotationPt.Symbol (s,0);;

let rec mk_prods l t =
  match l with
    [] -> t
  | hd::tl -> NotationPt.Binder (`Forall, (mk_id hd, None), mk_prods tl t)
;;

let mk_appl =
 function
    [] -> assert false
  | [x] -> x
  | l -> NotationPt.Appl l
;;

let rec iter f n acc =
  if n < 0 then acc
  else iter f (n-1) (f n acc)
;;

let subst_metasenv_and_fix_names status =
  let u,h,metasenv, subst,o = status#obj in
  let o = 
    NCicUntrusted.map_obj_kind ~skip_body:true 
     (NCicUntrusted.apply_subst status subst []) o
  in
   status#set_obj(u,h,NCicUntrusted.apply_subst_metasenv status subst metasenv,subst,o)
;;

(* needed to workaround a weakness of the refiner? *)
let rec generalize0_tac tl s =
  match tl with
  | [] -> s
  | t0::tl0 -> NTactics.generalize0_tac [t0] (generalize0_tac tl0 s)
;;


(* input: nome della variabile riscritta
 * output: lista dei nomi delle variabili il cui tipo dipende dall'input *)
let cascade_select_in_ctx status ~subst ctx skip iname =
  let lctx, rctx = HExtlib.split_nth (iname - 1) ctx in
  let lctx = List.rev lctx in
  let rec rm_last = function
      [] | [_] -> []
    | hd::tl -> hd::(rm_last tl)
  in

  let indices,_ = List.fold_left
       (fun (acc,context) item -> 
          match item with
            | n,(NCic.Decl s | NCic.Def (s,_)) 
                  when (not (List.for_all (fun x -> NCicTypeChecker.does_not_occur status ~subst context (x-1) x s) acc)
                   && not (List.mem n skip)) ->
                List.iter (fun m -> pp (lazy ("acc has " ^ (string_of_int m)))) acc;
                pp (lazy ("acc occurs in the type of " ^ n));
                (1::List.map ((+) 1) acc, item::context)
            | _ -> (List.map ((+) 1) acc, item::context))
       ([1], rctx) lctx in
    let indices = rm_last indices in
    let res = List.map (fun n -> let s,_ = List.nth ctx (n-1) in s) indices in
    List.iter (fun n -> pp (lazy n)) res;
    pp (lazy (status#ppcontext ~metasenv:[] ~subst ctx));
    res, indices
;;

let rec mk_fresh_name ctx firstch n =
  let candidate = (String.make 1 firstch) ^ (string_of_int n) in
  if (List.for_all (fun (s,_) -> s <> candidate) ctx) then candidate
  else mk_fresh_name ctx firstch (n+1)
;;

let arg_list nleft t =
  let rec drop_prods n t =
    if n <= 0 then t
    else match t with
      | NCic.Prod (_,_,ta) -> drop_prods (n-1) ta
      | _ -> raise (Failure "drop_prods")
  in
  let rec aux = function
    | NCic.Prod (_,so,ta) -> so::aux ta
    | _ -> []
  in aux (drop_prods nleft t)
;;

let nargs it nleft consno =
  pp (lazy (Printf.sprintf "nargs %d %d" nleft consno));
  let _,indname,_,cl = it in
  let _,_,t_k = List.nth cl consno in
  List.length (arg_list nleft t_k) ;;

let default_pattern = "",0,(None,[],Some NotationPt.UserInput);; 
let prod_pattern = 
  "",0,(None,[],Some NotationPt.Binder 
    (`Pi, (mk_id "_",Some (NotationPt.Appl
      [ NotationPt.Implicit `JustOne
      ; NotationPt.Implicit `JustOne
      ; NotationPt.UserInput
      ; NotationPt.Implicit `JustOne ])), 
  NotationPt.Implicit `JustOne));;

let prod_pattern_jm = 
  "",0,(None,[],Some NotationPt.Binder 
    (`Pi, (mk_id "_",Some (NotationPt.Appl
      [ NotationPt.Implicit `JustOne
      ; NotationPt.Implicit `JustOne
      ; NotationPt.UserInput
      ; NotationPt.Implicit `JustOne
      ; NotationPt.Implicit `JustOne ])),
  NotationPt.Implicit `JustOne));;

let hp_pattern n = 
  "",0,(None,[n, NotationPt.Appl
      [ NotationPt.Implicit `JustOne
      ; NotationPt.Implicit `JustOne
      ; NotationPt.UserInput
      ; NotationPt.Implicit `JustOne ] ], 
  None);;

let hp_pattern_jm n = 
  "",0,(None,[n, NotationPt.Appl
      [ NotationPt.Implicit `JustOne
      ; NotationPt.Implicit `JustOne
      ; NotationPt.UserInput
      ; NotationPt.Implicit `JustOne
      ; NotationPt.Implicit `JustOne ] ], 
  None);;

(* creates the discrimination = injection+contradiction principle *)
exception ConstructorTooBig of string;;

let mk_discriminator ~use_jmeq ?(force=false) name it leftno status baseuri =
  let itnargs = 
    let _,_,arity,_ = it in 
    List.length (arg_list 0 arity) in
  let _,itname,_,_ = it in
  let params = List.map (fun x -> "a" ^ string_of_int x) (HExtlib.list_seq 1 (itnargs+1)) in
  let xyty = mk_appl (List.map mk_id (itname::params)) in

  (* PHASE 1: derive the type of the discriminator (we'll name it "principle") *)

  let mk_eq tys ts us es n =
    if use_jmeq then
      mk_appl [mk_id "jmeq";
               NotationPt.Implicit `JustOne; List.nth ts n;
               NotationPt.Implicit `JustOne; List.nth us n] 
    else
    (* eqty = Tn u0 e0...un-1 en-1 *)
    let eqty = mk_appl 
                 (List.nth tys n :: iter (fun i acc -> 
                                           List.nth us i::
                                           List.nth es i:: acc) 
                                     (n-1) []) in

    (* params = [T0;t0;...;Tn;tn;u0;e0;un-1;en-1] *)
    let params = iter (fun i acc -> 
                         List.nth tys i ::
                         List.nth ts i :: acc) n
                     (iter (fun i acc ->
                            List.nth us i::
                            List.nth es i:: acc) (n-1) []) in
    mk_appl [mk_id "eq"; eqty;
                        mk_appl (mk_id ("R" ^ string_of_int n) :: params);
                        List.nth us n]

  in
    
  let _,_,_,cl = it in

  let kname (*it*) j =
    let _,name,_ = List.nth cl j in
    name
  in

  let branch i j ts us = 
    let nargs = nargs it leftno i in
    let es = List.map (fun x -> mk_id ("e" ^ string_of_int x)) (HExtlib.list_seq 0 nargs) in
    let tys = List.map 
                (fun x -> iter 
                  (fun i acc -> 
                    NotationPt.Binder (`Lambda, (mk_id ("x" ^ string_of_int i), None),
                    NotationPt.Binder (`Lambda, (mk_id ("p" ^ string_of_int i), None),
                    acc))) (x-1) 
                 (NotationPt.Implicit (`Tagged ("T" ^ (string_of_int x)))))
               (HExtlib.list_seq 0 nargs) in
    let tys = tys @ 
      [iter (fun i acc -> 
        NotationPt.Binder (`Lambda, (mk_id ("x" ^ string_of_int i), None),
        NotationPt.Binder (`Lambda, (mk_id ("p" ^ string_of_int i), None),
        acc))) (nargs-1)
        (mk_appl [mk_id "eq"; NotationPt.Implicit `JustOne;
          mk_appl (mk_id (kname i)::
           List.map (fun x -> mk_id ("x" ^string_of_int x))
              (HExtlib.list_seq 0 (List.length ts)));
              mk_appl (mk_id (kname j)::us)])]
    in
    (** NotationPt.Binder (`Lambda, (mk_id "e", 
      Some (mk_appl 
        [mk_id "eq";
         NotationPt.Implicit `JustOne;
         mk_appl (mk_id (kname it i)::ts);
         mk_appl (mk_id (kname it j)::us)])),
    let ts = ts @ [mk_id "e"] in 
    let refl2 = mk_appl
                  [mk_id "refl";
                   NotationPt.Implicit `JustOne;
                   mk_appl (mk_id (kname it j)::us)] in
    let us = us @ [refl2] in *)
    NotationPt.Binder (`Forall, (mk_id "P", Some (NotationPt.Sort (`NType "1") )),
      if i = j then 
       NotationPt.Binder (`Forall, (mk_id "_",
        Some (iter (fun i acc -> 
              NotationPt.Binder (`Forall, (List.nth es i, Some (mk_eq tys ts us es i)), acc))
              (nargs-1) 
              (** (NotationPt.Binder (`Forall, (mk_id "_", 
                Some (mk_eq tys ts us es nargs)),*)
                (mk_id "P"))), mk_id "P")
      else mk_id "P")
  in

  let inner i ts = NotationPt.Case 
              (mk_id "y",None,
               (*Some (NotationPt.Binder (`Lambda, (mk_id "y",None), 
                 NotationPt.Binder (`Forall, (mk_id "_", Some
                 (mk_appl [mk_id "eq";NotationPt.Implicit
                 `JustOne;(*NotationPt.Implicit `JustOne*)
                  mk_appl (mk_id (kname it i)::ts);mk_id "y"])),
                 NotationPt.Implicit `JustOne )))*)
                  None,
                  List.map
                  (fun j -> 
                     let nargs_kty = nargs it leftno j in
                     let us = iter (fun m acc -> mk_id ("u" ^ (string_of_int m))::acc) 
                                (nargs_kty - 1) [] in
                     let nones = 
                       iter (fun _ acc -> None::acc) (nargs_kty - 1) [] in
                     NotationPt.Pattern (kname j,
                                            None,
                                            List.combine us nones), 
                                branch i j ts us)
                  (HExtlib.list_seq 0 (List.length cl)))
  in
  let outer = NotationPt.Case
                (mk_id "x",None,
                 None ,
                 List.map
                   (fun i -> 
                      let nargs_kty = nargs it leftno i in
                      if (nargs_kty > 5 && not use_jmeq && not force) then raise (ConstructorTooBig (kname i)); 
                      let ts = iter (fun m acc -> mk_id ("t" ^ (string_of_int m))::acc)
                                 (nargs_kty - 1) [] in
                     let nones = 
                       iter (fun _ acc -> None::acc) (nargs_kty - 1) [] in
                      NotationPt.Pattern (kname i,
                                             None,
                                             List.combine ts nones),
                                inner i ts)
                   (HExtlib.list_seq 0 (List.length cl))) in
  let principle = 
    mk_prods params (NotationPt.Binder (`Forall, (mk_id "x",
                               Some xyty),
                           NotationPt.Binder (`Forall, (mk_id "y", Some xyty),
                            (if use_jmeq then
                             NotationPt.Binder (`Forall, (mk_id "e",
                              Some (mk_appl
                               [mk_sym "jmsimeq"; NotationPt.Implicit `JustOne; mk_id "x";
                                                  NotationPt.Implicit `JustOne; mk_id "y"])),
                                                  outer)
                            else 
                              NotationPt.Binder (`Forall, (mk_id "e",
                              Some (mk_appl [mk_sym "eq";NotationPt.Implicit `JustOne; mk_id "x"; mk_id "y"])),
                             outer)))))
  in
  pp (lazy ("discriminator = " ^ (NotationPp.pp_term status principle)));

  (* PHASE 2: create the object for the proof of the principle: we'll name it
   * "theorem" *)
  let status, theorem =
   let attrs = `Generated, `Theorem, `DiscriminationPrinciple in
   GrafiteDisambiguate.disambiguate_nobj status ~baseuri
    (baseuri ^ name ^ ".def",0,
      NotationPt.Theorem
       (name, principle, Some (NotationPt.Implicit (`Tagged "inv")), attrs))
  in 
  let uri,height,nmenv,nsubst,nobj = theorem in
  let ninitial_stack = Continuationals.Stack.of_nmetasenv nmenv in
  let status = status#set_obj theorem in
  let status = status#set_stack ninitial_stack in
  let status = subst_metasenv_and_fix_names status in

  (* PHASE 3: we finally prove the discrimination principle *)
  let dbranch it ~use_jmeq leftno consno =
    let refl_id = mk_sym "refl" in
    pp (lazy (Printf.sprintf "dbranch %d %d" leftno consno));
    let nlist = HExtlib.list_seq 0 (nargs it leftno consno) in
    (* (\forall ...\forall P.\forall DH : ( ... = ... -> P). P) *)
    let params = List.map (fun x -> NTactics.intro_tac ("a" ^ string_of_int x)) nlist in
        (* NTactics.reduce_tac ~reduction:(`Normalize true)
         * ~where:default_pattern::*)
        params @ [
        NTactics.intro_tac "P";
        NTactics.intro_tac "DH";
        NTactics.apply_tac ("",0,mk_id "DH");
        NTactics.apply_tac ("",0,refl_id); (* well, it works even if no goal is selected after applying DH... *)
    ] in
  let dbranches it ~use_jmeq leftno =
    pp (lazy (Printf.sprintf "dbranches %d" leftno));
    let nbranches = List.length cl in 
    let branches = iter (fun n acc -> 
      let m = nbranches - n - 1 in
      if m = 0 then acc @ (dbranch it ~use_jmeq leftno m)
      else acc @ NTactics.shift_tac :: (dbranch it ~use_jmeq
      leftno m))
      (nbranches-1) [] in
    if nbranches > 1 then
         NTactics.branch_tac ~force:false:: branches @ [NTactics.merge_tac]
    else branches
  in
  let print_tac s status = pp s ; status in 

  let status =
   NTactics.block_tac (
    [print_tac (lazy "ci sono") (*;
     NTactics.reduce_tac ~reduction:(`Normalize true) ~where:default_pattern *)
    ]
  @ List.map (fun x -> NTactics.intro_tac x) params @
    [NTactics.intro_tac "x";
     NTactics.intro_tac "y";
     NTactics.intro_tac "Deq";
    print_tac (lazy "ci sono 2");
     NTactics.rewrite_tac ~dir:`RightToLeft ~what:("",0,mk_id "Deq") ~where:default_pattern;
     NTactics.cases_tac ~what:("",0,mk_id "x") ~where:default_pattern]
  @ dbranches it ~use_jmeq leftno) status
  in status, status#obj
;;

let hd_of_term = function
  | NCic.Appl (hd::_) -> hd
  | t -> t
;;

let name_of_rel ~context rel =
  let s, _ = List.nth context (rel-1) in s
;;

(* let lookup_in_ctx ~context n =
  List.nth context ((List.length context) - n - 1)
;;*)

let discriminate_tac ~context cur_eq status =
  pp (lazy (Printf.sprintf "discriminate: equation %s" (name_of_rel ~context cur_eq)));

  
  let eq_name,(NCic.Decl s | NCic.Def (s,_)) = List.nth context (cur_eq-1) in
  let _,ctx' = HExtlib.split_nth cur_eq context in
  let status, s = NTacStatus.whd status ctx' (mk_cic_term ctx' s) in
  let status, s = term_of_cic_term status s ctx' in
  let status,it,use_jmeq = 
    let it,use_jmeq = match s with
      | NCic.Appl [_;it;_;_] -> it,false
      | NCic.Appl [_;it;_;_;_] -> it,true
      | _ -> assert false in
    (* XXX: serve? ho già fatto whd *)
    let status, it = whd status ctx' (mk_cic_term ctx' it) in
    let status, it = term_of_cic_term status it ctx' in
    let _uri,indtyno,its = match it with
      | NCic.Const (NReference.Ref (uri, NReference.Ind (_,indtyno,_)) as r) 
      | NCic.Appl (NCic.Const 
          (NReference.Ref (uri, NReference.Ind (_,indtyno,_)) as r)::_) -> 
        uri, indtyno, NCicEnvironment.get_checked_indtys status r
      | _ -> pp (lazy ("discriminate: indty ="  ^ status#ppterm
                  ~metasenv:[] ~subst:[] ~context:[] it)) ; assert false in
    let _,_,its,_,_ = its in
    status,List.nth its indtyno, use_jmeq
  in
  
  let itnargs = 
    let _,_,arity,_ = it in 
    List.length (arg_list 0 arity) in
  let _,itname,_,_ = it in
  let params = List.map (fun x -> "a" ^ string_of_int x) (HExtlib.list_seq 1 (itnargs+1)) in
  let principle_name = 
    if use_jmeq then itname ^ "_jmdiscr"
    else itname ^ "_discr"
  in
  pp (lazy ("apply (" ^ principle_name ^ " " ^
            (String.concat "" (HExtlib.mk_list "?" (List.length params + 2))) ^
            " " ^ eq_name ^ ")"));
  NTactics.apply_tac ("",0,mk_appl ([mk_id principle_name]@
                                HExtlib.mk_list (NotationPt.Implicit `JustOne) (List.length params + 2) @
                                [mk_id eq_name ])) status
;;

let saturate_skip status context skip =
  HExtlib.list_uniq
    (List.fold_left
      (fun acc x -> 
         let ix = HExtlib.list_index ((=) x) (List.map fst context)
         in match ix with
         | None -> acc
	 | Some (i,_) -> 
            fst (cascade_select_in_ctx status ~subst:(get_subst status) context [] (i+1)) @ acc) skip skip)
;;
      
let subst_tac ~context ~dir skip cur_eq =
  fun status as oldstatus ->
  let eq_name,(NCic.Decl s | NCic.Def (s,_)) = List.nth context (cur_eq-1) in
  let _,ctx' = HExtlib.split_nth cur_eq context in
  let status, s = NTacStatus.whd status ctx' (mk_cic_term ctx' s) in
  let status, s = term_of_cic_term status s ctx' in
  let skip = saturate_skip status context skip in
  pp (lazy (Printf.sprintf "subst: equation %s" eq_name));
    let l, r = match s with
      | NCic.Appl [_;_;t1;t2] | NCic.Appl [_;_;t1;_;t2] -> t1,t2
      | _ -> assert false in
    let var = match dir with
      | `LeftToRight -> l
      | `RightToLeft -> r in
    (* let var = match var with
      | NCic.Rel i -> i
      | _ -> assert false in *)
    let names_to_gen, _ = 
      match var with 
      | NCic.Rel var ->
        cascade_select_in_ctx status ~subst:(get_subst status) context skip (var+cur_eq)
      | _ -> cascade_select_in_ctx status ~subst:(get_subst status) context skip cur_eq in
    let varname = match var with
      | NCic.Rel var -> 
          let name,_ = List.nth context (var+cur_eq-1) in
	  HLog.warn (Printf.sprintf "destruct: trying to remove variable: %s" name);
	  [name]
      | _ -> []
    in      
    let names_to_gen = List.filter (fun n -> n <> eq_name) names_to_gen in
    if (List.exists (fun x -> List.mem x skip) names_to_gen)
      then oldstatus
    else 
    let gen_tac x =
      (fun s -> 
      let x' = String.concat " " x in
      let x = List.map mk_id x in
      (* let s = NTactics.print_tac false ("@generalize " ^ x') s in *)
      generalize0_tac x s) in
    NTactics.block_tac (
                (* (List.map gen_tac names_to_gen)@ *)
            [gen_tac (List.rev names_to_gen);
                        NTactics.clear_tac names_to_gen;
                 NTactics.rewrite_tac ~dir 
                   ~what:("",0,mk_id eq_name) ~where:default_pattern;
(*                 NTactics.reduce_tac ~reduction:(`Normalize true)
                   ~where:default_pattern;*)
                 (* XXX: temo che la clear multipla funzioni bene soltanto se
                  * gli identificatori sono nell'ordine giusto.
                  * Per non saper né leggere né scrivere, usiamo due clear
                  * invece di una *)
                 NTactics.try_tac (NTactics.clear_tac [eq_name]);
		 NTactics.try_tac (NTactics.clear_tac varname);
]@
                 (List.map NTactics.intro_tac (List.rev names_to_gen))) status
;;

let clearid_tac ~context skip cur_eq =
  fun status ->
  let eq_name,(NCic.Decl s | NCic.Def (s,_)) = List.nth context (cur_eq-1) in
  let _,ctx' = HExtlib.split_nth cur_eq context in
  let status, s = NTacStatus.whd status ctx' (mk_cic_term ctx' s) in
  let status, s = term_of_cic_term status s ctx' in
  let skip = saturate_skip status context skip in

  pp (lazy (Printf.sprintf "clearid: equation %s" eq_name));
  let streicher_id = mk_id "streicherK" in
  let names_to_gen, _ = 
    cascade_select_in_ctx status ~subst:(get_subst status) context skip cur_eq in
  let gen_tac x = generalize0_tac (List.map mk_id x) in
  
  match s with
  (* jmeq *)
  | NCic.Appl [_;_;_;_;_] ->
      let names_to_gen = List.rev names_to_gen in
      (*let gen_eq = NTactics.generalize_tac
       ~where:("",0,(Some (mk_appl [mk_id "jmeq_to_eq";
                                    NotationPt.Implicit `JustOne; 
                                    NotationPt.Implicit `JustOne; 
                                    NotationPt.Implicit `JustOne; 
                                    mk_id eq_name]),[], Some
                                    NotationPt.UserInput)) in*)
      let gen_eq = generalize0_tac 
                          [mk_appl [mk_id "jmeq_to_eq";
                                    NotationPt.Implicit `JustOne; 
                                    NotationPt.Implicit `JustOne; 
                                    NotationPt.Implicit `JustOne; 
                                    mk_id eq_name]] in
      NTactics.block_tac ((gen_tac (List.rev names_to_gen))::gen_eq::
                  [NTactics.clear_tac names_to_gen;
                   NTactics.try_tac (NTactics.clear_tac [eq_name]);
                   NTactics.apply_tac ("",0, mk_appl [streicher_id;
  						    NotationPt.Implicit `JustOne;
  						    NotationPt.Implicit `JustOne;
  						    NotationPt.Implicit `JustOne;
  						    NotationPt.Implicit `JustOne]);
                   ] @
                   (List.map NTactics.intro_tac names_to_gen)) status

    (* leibniz *)
  | NCic.Appl [_;_;_;_] ->
      begin
       let names_to_gen, _ = 
         cascade_select_in_ctx status ~subst:(get_subst status) context skip cur_eq in
       let names_to_gen = eq_name :: (List.rev names_to_gen) in
       NTactics.block_tac ((gen_tac names_to_gen)::
                   [NTactics.clear_tac names_to_gen;
                    NTactics.apply_tac ("",0, mk_appl [streicher_id;
   						    NotationPt.Implicit `JustOne;
   						    NotationPt.Implicit `JustOne;
   						    NotationPt.Implicit `JustOne;
   						    NotationPt.Implicit `JustOne])
   (*                 NTactics.reduce_tac ~reduction:(`Normalize true) 
                      ~where:default_pattern *)
                    ] @
                    let names_to_intro = List.tl names_to_gen in
                    (List.map NTactics.intro_tac names_to_intro)) status
     end
  | _ -> assert false

;;

let get_ctx st goal =
    ctx_of (get_goalty st goal)
;;

(* = select + classify *)
let select_eq ctx acc domain status goal =
  let classify ~use_jmeq ~subst ctx' l r =
    (* FIXME: metasenv *)
    if NCicReduction.are_convertible status ~metasenv:[] ~subst ctx' l r 
      then status, `Identity
      else status, (match hd_of_term l, hd_of_term r with
        | NCic.Const (NReference.Ref (_,NReference.Con (_,ki,nleft)) as kref),
          NCic.Const (NReference.Ref (_,NReference.Con (_,kj,_))) -> 
            if ki != kj then `Discriminate (0,true, use_jmeq)
            else
              let rit = NReference.mk_indty true kref in
              let _,_,its,_,itno = NCicEnvironment.get_checked_indtys status rit in 
              let it = List.nth its itno in
              let newprods = nargs it nleft (ki-1) in
              `Discriminate (newprods, false, use_jmeq) 
        | NCic.Rel j, _  
            when NCicTypeChecker.does_not_occur status ~subst ctx' (j-1) j r
              && l = NCic.Rel j -> `Subst `LeftToRight
        | _, NCic.Rel j 
            when NCicTypeChecker.does_not_occur status ~subst ctx' (j-1) j l 
              && r = NCic.Rel j -> `Subst `RightToLeft
        | (NCic.Rel _, _ | _, NCic.Rel _ ) -> `Cycle (* could be a blob too... *)
        | _ -> `Blob) in
  let rec aux i =
    try
      let index = List.length ctx - i in
      pp (lazy ("provo classify di index = " ^string_of_int index));
      match (List.nth ctx (index - 1)) with
      | n, (NCic.Decl ty | NCic.Def (ty,_)) ->
          (let _,ctx_ty = HExtlib.split_nth index ctx in 
           let status, ty = NTacStatus.whd status ctx_ty (mk_cic_term ctx_ty ty) in
           let status, ty = term_of_cic_term status ty ctx_ty in
           pp (lazy (Printf.sprintf "select_eq tries %s" (status#ppterm ~context:ctx_ty ~subst:[] ~metasenv:[] ty)));
           let status, kind = match ty with
           | NCic.Appl [NCic.Const (NReference.Ref (u,_)) ;_;l;r] 
               when NUri.name_of_uri u = "eq" ->
               classify ~use_jmeq:false ~subst:(get_subst status) ctx_ty l r
           | NCic.Appl [NCic.Const (NReference.Ref (u,_)) ;lty;l;rty;r]
               when NUri.name_of_uri u = "jmeq" && 
                 NCicReduction.are_convertible status ~metasenv:[] 
                   ~subst:(get_subst status) ctx_ty lty rty
               -> classify ~use_jmeq:true ~subst:(get_subst status) ctx_ty l r
           | _ -> status, `NonEq 
           in match kind with
              | `Identity ->
                  let status, goalty = term_of_cic_term status (get_goalty status goal) ctx in
                     status, Some (List.length ctx - i), kind
              | `Cycle | `Blob | `NonEq -> aux (i+1) (* XXX: skip cyclic/blob equations for now *)
              | _ -> 
                 if (List.for_all (fun x -> x <> n) acc) && 
                    (List.exists (fun x -> x = n) domain) 
		 then status, Some (List.length ctx - i), kind
                 else aux (i+1))
    with Failure _ | Invalid_argument _ -> status, None, `Blob
  in aux 0
;;

let tagged_intro_tac curtag name =
  match curtag with
  | `Notag -> NTactics.intro_tac name
  | `Eq use_jmeq ->
      NTactics.block_tac
        [ NTactics.intro_tac name 
        ; NTactics.reduce_tac 
            ~reduction:(`Whd true) ~where:((if use_jmeq then hp_pattern_jm else hp_pattern) name) ]
        
(*        status in
      distribute_tac (fun s g ->
        let eq_name,(NCic.Decl s | NCic.Def (s,_)) = List.nth context (cur_eq-1) in
        let _,ctx' = HExtlib.split_nth cur_eq context in
        let status, s = NTacStatus.whd status ctx' (mk_cic_term ctx' s) in
        let status, s = term_of_cic_term status s ctx' in
        let use_jmeq =
          match s with
          | NCic.Appl [_;it;t1;t2] -> false
          | NCic.Appl [_;it;t1;_;t2] -> true
          | _ -> assert false in
      ) status
    let it, t1, t2, use_jmeq = match s with
      | NCic.Appl [_;it;t1;t2] -> it,t1,t2,false
      | NCic.Appl [_;it;t1;_;t2] -> it,t1,t2,true
      | _ -> assert false in
           [ NTactics.intro_tac name
           ; NTactics.reduce_tac ~reduction:(`Whd true) ~where:prod_pattern ]*)
;;

let rec destruct_tac0 tags acc domain skip status goal =
  let pptag = function
    | `Eq false -> "eq"
    | `Eq true -> "jmeq"
    | `Notag -> "reg"
  in
  let pptags tags = String.concat ", " (List.map pptag tags) in
  let ctx = get_ctx status goal in
  let subst = get_subst status in
  let get_newgoal os ns ogoal =
    let go, gc = NTactics.compare_statuses ~past:os ~present:ns in
    let go' = ([ogoal] @- gc) @+ go in
      match go' with [] -> assert false | g::_ -> g
  in
  let status, selection, kind  = select_eq ctx acc domain status goal in
  pp (lazy ("destruct: acc is " ^ String.concat "," acc ));
  match selection, kind with
  | None, _ -> 
    pp (lazy (Printf.sprintf 
       "destruct: no selection, context is %s, stack is %s" 
       (status#ppcontext ~metasenv:[] ~subst ctx) (pptags tags)));
     (match tags with 
      | [] -> status
      | curtag::tags' ->
        let fresh = mk_fresh_name ctx 'e' 0 in 
        let status' = NTactics.exec (tagged_intro_tac curtag fresh) status goal in
        destruct_tac0 tags' acc (fresh::domain) skip status' 
          (get_newgoal status status' goal))
  | Some cur_eq, `Discriminate (newprods,conflict,use_jmeq) -> 
    pp (lazy (Printf.sprintf 
      "destruct: discriminate - nselection is %d, context is %s,stack is %s" 
       cur_eq (status#ppcontext ~metasenv:[] ~subst ctx) (pptags tags)));
      let status' = NTactics.exec (discriminate_tac ~context:ctx cur_eq) status goal in
      if conflict then status'
      else 
        let newtags = HExtlib.mk_list (`Eq use_jmeq) newprods in
        destruct_tac0 (newtags@tags) 
             (name_of_rel ~context:ctx cur_eq::acc) 
             (List.filter (fun x -> x <> name_of_rel ~context:ctx cur_eq) domain)
             skip 
             status' (get_newgoal status status' goal)
  | Some cur_eq, `Subst dir ->
    pp (lazy (Printf.sprintf 
      "destruct: subst - selection is %d, context is %s, stack is %s" 
        cur_eq (status#ppcontext ~metasenv:[] ~subst ctx) (pptags tags)));
    let status' = NTactics.exec (subst_tac ~context:ctx ~dir skip cur_eq) status goal in
      pp (lazy (Printf.sprintf " ctx after subst = %s" (status#ppcontext ~metasenv:[] ~subst (get_ctx status' (get_newgoal status status' goal)))));
    let eq_name,_ = List.nth ctx (cur_eq-1) in
    let newgoal = get_newgoal status status' goal in
    let has_cleared = 
     try 
       let _ = NTactics.find_in_context eq_name (get_ctx status' newgoal) in false
     with 
      | Sys.Break as e -> raise e
      |_ -> true in
    let rm_eq b l = if b then List.filter (fun x -> x <> eq_name) l else l in
    let acc = rm_eq has_cleared acc in
    let skip = rm_eq has_cleared skip in
    let domain = rm_eq has_cleared domain in
      destruct_tac0 tags acc domain skip status' newgoal
 | Some cur_eq, `Identity ->
    pp (lazy (Printf.sprintf 
      "destruct: identity - selection is %d, context is %s, stack is %s" 
        cur_eq (status#ppcontext ~metasenv:[] ~subst ctx) (pptags tags)));
      let eq_name,_ = List.nth ctx (cur_eq-1) in
      let status' = NTactics.exec (clearid_tac ~context:ctx skip cur_eq) status goal in
      let newgoal = get_newgoal status status' goal in
      let has_cleared = 
       try 
         let _ = NTactics.find_in_context eq_name (get_ctx status' newgoal) in false
       with 
         | Sys.Break as e -> raise e         
	 | _ -> true in
      let rm_eq b l = if b then List.filter (fun x -> x <> eq_name) l else l in
      let acc = rm_eq has_cleared acc in
      let skip = rm_eq has_cleared skip in
      let domain = rm_eq has_cleared domain in
        destruct_tac0 tags acc domain skip status' newgoal
  | Some cur_eq, `Cycle -> (* TODO, should never happen *)
    pp (lazy (Printf.sprintf 
      "destruct: cycle - selection is %d, context is %s, stack is %s" 
        cur_eq (status#ppcontext ~metasenv:[] ~subst ctx) (pptags tags)));
      assert false
  | Some cur_eq, `Blob ->
    pp (lazy (Printf.sprintf 
      "destruct: blob - selection is %d, context is %s, stack is %s"
      cur_eq (status#ppcontext ~metasenv:[] ~subst ctx) (pptags tags)));
      assert false
  | _ -> assert false
;;

let destruct_tac dom skip s = 
  NTactics.distribute_tac 
    (fun s' g -> 
     let ctx = get_ctx s' g in
     let domain = match dom with
       | None -> List.map (fun (n,_) -> n) ctx
       | Some l -> l 
     in
     destruct_tac0 [] [] domain skip s' g) s;;
