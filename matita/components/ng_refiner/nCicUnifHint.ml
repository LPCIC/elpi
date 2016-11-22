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

(* $Id: nCicRefiner.mli 9227 2008-11-21 16:00:06Z tassi $ *)

module Ref = NReference

let debug s = prerr_endline (Lazy.force s);;
let debug _ = ();;

module HOT : Set.OrderedType 
with type t = int * NCic.term  * NCic.term * NCic.term = 
  struct
        (* precedence, skel1, skel2, term *)
        type t = int * NCic.term * NCic.term * NCic.term
        let compare = Pervasives.compare
  end

module EOT : Set.OrderedType 
with type t = int * NCic.term =
  struct
        type t = int * NCic.term 
        let compare = Pervasives.compare
  end

module HintSet = Set.Make(HOT)
module EqSet = Set.Make(EOT)

module HDB = 
  Discrimination_tree.Make(NDiscriminationTree.NCicIndexable)(HintSet)

module EQDB = 
  Discrimination_tree.Make(NDiscriminationTree.NCicIndexable)(EqSet)

type db =
  HDB.t * (* hint database: (dummy A B)[?] |-> \forall X.(summy a b)[X] *)
  EQDB.t (* eqclass DB: A[?] |-> \forall X.B[X] and viceversa *)

exception HintNotValid

let skel_dummy = NCic.Implicit `Type;;

class type g_status =
 object
  method uhint_db: db
 end

class virtual status =
 object
  inherit NCic.status
  val db = HDB.empty, EQDB.empty
  method uhint_db = db
  method set_uhint_db v = {< db = v >}
  method set_unifhint_status
   : 'status. #g_status as 'status -> 'self
   = fun o -> {< db = o#uhint_db >}
 end

let dummy =
 let uri = NUri.uri_of_string "cic:/matita/dummy/dec.con" in
 NCic.Const (Ref.reference_of_spec uri Ref.Decl);;

let pair t1 t2 = (NCic.Appl [dummy;t1;t2]) ;;

let index_hint status context t1 t2 precedence =
  assert (
    (match t1 with
    | NCic.Meta _ | NCic.Appl (NCic.Meta _ :: _) -> false | _ -> true)
    &&
    (match t2 with
    | NCic.Meta _ | NCic.Appl (NCic.Meta _ :: _) -> false | _ -> true)
  );
  (* here we do not use skel_dummy since it could cause an assert false in 
   * the subst function that lives in the kernel *)
  let hole = NCic.Meta (-1,(0,NCic.Irl 0)) in
  let t1_skeleton = 
    List.fold_left (fun t _ -> NCicSubstitution.subst status hole t) t1 context
  in
  let t2_skeleton = 
    List.fold_left (fun t _ -> NCicSubstitution.subst status hole t) t2 context
  in
  let rec cleanup_skeleton () = function
    | NCic.Meta _ -> skel_dummy 
    | t -> NCicUtils.map status (fun _ () -> ()) () cleanup_skeleton t
  in
  let t1_skeleton = cleanup_skeleton () t1_skeleton in
  let t2_skeleton = cleanup_skeleton () t2_skeleton in
  let src = pair t1_skeleton t2_skeleton in
  let ctx2abstractions context t = 
    List.fold_left 
     (fun t (n,e) -> 
        match e with
        | NCic.Decl ty -> NCic.Prod (n,ty,t)
        | NCic.Def (b,ty) -> NCic.LetIn (n,ty,b,t))
      t context 
  in
  let data_hint = 
    precedence, t1_skeleton, t2_skeleton, ctx2abstractions context (pair t1 t2)
  in
  let data_t1 = t2_skeleton in
  let data_t2 = t1_skeleton in

  debug(lazy ("INDEXING: " ^ 
    status#ppterm ~metasenv:[] ~subst:[] ~context:[] src ^ " |==> " ^
    status#ppterm ~metasenv:[] ~subst:[] ~context:[] 
      (let _,x,_,_ = data_hint in x)));

  status#set_uhint_db (
      HDB.index (fst (status#uhint_db)) src data_hint,
      EQDB.index  
        (EQDB.index (snd (status#uhint_db)) t2_skeleton (precedence, data_t2))
        t1_skeleton (precedence, data_t1))
;;

let add_user_provided_hint status t precedence =
  let c, a, b = 
    let rec aux ctx = function
      | NCic.Appl l ->
          (match List.rev l with
          | b::a::_ -> 
              if
                 let ty_a = 
                   NCicTypeChecker.typeof status ~metasenv:[] ~subst:[] ctx a
                 in
                 let ty_b = 
                   NCicTypeChecker.typeof status ~metasenv:[] ~subst:[] ctx b
                 in
                 NCicReduction.are_convertible status
                  ~metasenv:[] ~subst:[] ctx ty_a ty_b              
                 &&     
                 NCicReduction.are_convertible status
                  ~metasenv:[] ~subst:[] ctx a b              
              then ctx, a, b
              else raise HintNotValid
          | _ -> assert false)
      | NCic.Prod (n,s,t) -> aux ((n, NCic.Decl s) :: ctx) t
      | NCic.LetIn (n,ty,t,b) -> aux  ((n, NCic.Def (t,ty)) :: ctx) b
      | _ -> assert false
    in
      aux [] t
  in
   index_hint status c a b precedence
;;

(*
let db () = 
  let combine f l =
   List.flatten
     (let rec aux = function 
      | u1 :: tl -> List.map (f u1) tl :: aux tl
      | [] -> []
     in aux l)
  in
  let mk_hint (u1,_,_) (u2,_,_) = 
    let l = OCic2NCic.convert_obj u1 
      (fst (CicEnvironment.get_obj CicUniv.oblivion_ugraph u1)) in
    let r = OCic2NCic.convert_obj u2 
      (fst (CicEnvironment.get_obj CicUniv.oblivion_ugraph u2)) in
    match List.hd l,List.hd r with
    | (_,h1,_,_,NCic.Constant (_,_,Some l,_,_)), 
      (_,h2,_,_,NCic.Constant (_,_,Some r,_,_)) ->
        let rec aux ctx t1 t2 =
          match t1, t2 with
          | NCic.Lambda (n1,s1,b1), NCic.Lambda(_,s2,b2) ->
              if NCicReduction.are_convertible ~subst:[] ~metasenv:[] ctx s1 s2
              then aux ((n1, NCic.Decl s1) :: ctx) b1 b2
              else []
          | b1,b2 -> 
              if NCicReduction.are_convertible ~subst:[] ~metasenv:[] ctx b1 b2 
              then begin
              let rec mk_rels =  
                 function 0 -> [] | n -> NCic.Rel n :: mk_rels (n-1) 
              in 
              let n1 = 
                NCic.Appl (NCic.Const(OCic2NCic.reference_of_ouri 
                 u1 (Ref.Def h1)) :: mk_rels (List.length ctx))
              in
              let n2 = 
                NCic.Appl (NCic.Const(OCic2NCic.reference_of_ouri 
                 u2 (Ref.Def h2)) :: mk_rels (List.length ctx))
              in
                [ctx,b1,b2; ctx,b1,n2; ctx,n1,b2; ctx,n1,n2]
              end else []
        in
          aux [] l r
    | _ -> []
  in
  let _hints = 
    List.fold_left 
      (fun acc (_,_,l) -> 
          acc @ 
          if List.length l > 1 then 
           combine mk_hint l
          else [])
      [] (CoercDb.to_list (CoercDb.dump ()))
  in
  prerr_endline "MISTERO";
  assert false (* ERA
  List.fold_left 
    (fun db -> function 
     | (ctx,b1,b2) -> index_hint db ctx b1 b2 0)
    !user_db (List.flatten hints)
*)
;;
*)

let saturate status ?(delta=0) metasenv subst context ty goal_arity =
 assert (goal_arity >= 0);
  let rec aux metasenv = function
   | NCic.Prod (name,s,t) as ty ->
       let metasenv1, _, arg,_ = 
          NCicMetaSubst.mk_meta ~attrs:[`Name name] metasenv context
           ~with_type:s `IsTerm 
       in
       let t, metasenv1, args, pno = 
           aux metasenv1 (NCicSubstitution.subst status arg t) 
       in
       if pno + 1 = goal_arity then
         ty, metasenv, [], goal_arity+1
       else
         t, metasenv1, arg::args, pno+1
   | ty ->
        match NCicReduction.whd status ~subst context ty ~delta with
        | NCic.Prod _ as ty -> aux metasenv ty
        | _ -> ty, metasenv, [], 0 (* differs from the other impl in this line*)
  in
  let res, newmetasenv, arguments, _ = aux metasenv ty in
  res, newmetasenv, arguments
;;

let eq_class_of (status:#status) t1 = 
 let eq_class =
  if NDiscriminationTree.NCicIndexable.path_string_of t1 = 
     [Discrimination_tree.Variable]
  then
    [] (* if the trie is unable to handle the key, we skip the query since
          it sould retulr the whole content of the trie *)
  else
    let candidates = EQDB.retrieve_unifiables (snd status#uhint_db) t1 in
    let candidates = EqSet.elements candidates in
    let candidates = List.sort (fun (x,_) (y,_) -> compare x y) candidates in
    List.map snd candidates
 in
 debug(lazy("eq_class of: " ^ status#ppterm ~metasenv:[] ~context:[] ~subst:[]
   t1 ^ " is\n" ^ String.concat "\n" 
   (List.map (status#ppterm ~metasenv:[] ~context:[] ~subst:[]) eq_class)));
 eq_class   
;;

let look_for_hint (status:#status) metasenv subst context t1 t2 =
  if NDiscriminationTree.NCicIndexable.path_string_of t1 =
          [Discrimination_tree.Variable] || 
     NDiscriminationTree.NCicIndexable.path_string_of t2 =
             [Discrimination_tree.Variable] then [] else begin

  debug(lazy ("KEY1: "^status#ppterm ~metasenv ~subst ~context t1));
  debug(lazy ("KEY2: "^status#ppterm ~metasenv ~subst ~context t2));
(*
  HDB.iter status
   (fun p ds ->
      prerr_endline ("ENTRY: " ^
      NDiscriminationTree.NCicIndexable.string_of_path p ^ " |--> " ^
      String.concat "|" (List.map (status#ppterm ~metasenv:[] ~subst:[]
      ~context:[]) (HintSet.elements ds))));
*)
  let candidates1 = HDB.retrieve_unifiables (fst status#uhint_db) (pair t1 t2) in
  let candidates2 = HDB.retrieve_unifiables (fst status#uhint_db) (pair t2 t1) in
  let candidates1 = 
    List.map (fun (prec,_,_,ty) -> 
       prec,true,saturate status ~delta:max_int metasenv subst context ty 0) 
    (HintSet.elements candidates1) 
  in
  let candidates2 = 
    List.map (fun (prec,_,_,ty) -> 
       prec,false,saturate status ~delta:max_int metasenv subst context ty 0) 
    (HintSet.elements candidates2) 
  in
  let rc = 
    List.map
      (fun (p,b,(t,m,_)) ->
         let rec aux () (m,l as acc) = function
           | NCic.Meta _ as t -> acc, t
           | NCic.LetIn (name,ty,bo,t) ->
               let m,_,i,_=
                 NCicMetaSubst.mk_meta ~attrs:[`Name name] m context
                  ~with_type:ty `IsTerm 
               in
               let t = NCicSubstitution.subst status i t in
               aux () (m, (i,bo)::l) t
           | t -> NCicUntrusted.map_term_fold_a status (fun _ () -> ()) () aux acc t
         in
         let (m,l), t = aux () (m,[]) t in
         p,b,(t,m,l))
   (candidates1 @ candidates2)
  in
  let rc = 
  List.map
   (function 
    | (prec,true,(NCic.Appl [_; t1; t2],metasenv,l))-> prec,metasenv,(t1,t2),l
    | (prec,false,(NCic.Appl [_; t1; t2],metasenv,l))-> prec,metasenv,(t2,t1),l
    | _ -> assert false)
    rc
  in
  let rc = 
    List.sort (fun (x,_,_,_) (y,_,_,_) -> Pervasives.compare x y) rc
  in 
  let rc = List.map (fun (_,x,y,z) -> x,y,z) rc in

  debug(lazy ("Hints:"^
    String.concat "\n" (List.map 
     (fun (metasenv, (t1, t2), premises) ->
         ("\t" ^ String.concat ";  "
               (List.map (fun (a,b) -> 
                  status#ppterm ~margin:max_int ~metasenv ~subst ~context a ^
                  " =?= "^
                  status#ppterm ~margin:max_int ~metasenv ~subst ~context b)
               premises) ^     
             "  ==> "^
             status#ppterm ~margin:max_int ~metasenv ~subst ~context t1 ^
             " = "^status#ppterm ~margin:max_int ~metasenv ~subst ~context t2))
    rc)));

  rc
             end
;;

let pp_hint t p =
  let context, t = 
     let rec aux ctx = function
       | NCic.Prod (name, ty, rest) -> aux ((name, NCic.Decl ty) :: ctx) rest
       | t -> ctx, t
     in
      aux [] t
  in
  let recproblems, concl = 
    let rec aux ctx = function
      | NCic.LetIn (name,ty,bo,rest) -> aux ((name, NCic.Def(bo,ty))::ctx) rest
      | t -> ctx, t
    in
      aux [] t
  in
  let buff = Buffer.create 100 in
  let fmt = Format.formatter_of_buffer buff in
(*
  F.fprintf "@[<hov>"
   F.fprintf "@[<hov>"
(*    pp_ctx [] context *)
   F.fprintf "@]"
  F.fprintf "@;"
   F.fprintf "@[<hov>"
(*    pp_ctx context recproblems *)
   F.fprintf "@]"
  F.fprintf "\vdash@;";
    status#ppterm ~fmt ~context:(recproblems@context) ~subst:[] ~metasenv:[];
  F.fprintf "@]"
  F.fprintf formatter "@?";
  prerr_endline (Buffer.contents buff);
*)
()
;;

let generate_dot_file (status:#status) fmt =
  let module Pp = GraphvizPp.Dot in
  let h_db, _ = status#uhint_db in
  let names = ref [] in
  let id = ref 0 in
  let mangle l =
    try List.assoc l !names
    with Not_found ->
      incr id;
      names := (l,"node"^string_of_int!id) :: !names;
      List.assoc l !names
  in
  let nodes = ref [] in
  let edges = ref [] in
  HDB.iter h_db (fun _key dataset -> 
      List.iter
        (fun (precedence, l,r, hint) ->
            let l = 
              Str.global_substitute (Str.regexp "\n") (fun _ -> "")
               (status#ppterm 
                ~margin:max_int ~metasenv:[] ~context:[] ~subst:[] l) 
            in
            let r = 
              Str.global_substitute (Str.regexp "\n") (fun _ -> "")
               (status#ppterm 
                ~margin:max_int ~metasenv:[] ~context:[] ~subst:[] r)
            in
            let shint =  "???" (*
              string_of_int precedence ^ "..." ^
              Str.global_substitute (Str.regexp "\n") (fun _ -> "")
               (status#ppterm 
                ~margin:max_int ~metasenv:[] ~context:[] ~subst:[] hint)*)
            in
            nodes := (mangle l,l) :: (mangle r,r) :: !nodes;
            edges := (mangle l, mangle r, shint, precedence, hint) :: !edges)
        (HintSet.elements dataset);
    );
  List.iter (fun x, l -> Pp.node x ~attrs:["label",l] fmt) !nodes;
  List.iter (fun x, y, l, _, _ -> 
      Pp.raw (Printf.sprintf "%s -- %s [ label=\"%s\" ];\n" x y "?") fmt)
  !edges;
  edges := List.sort (fun (_,_,_,p1,_) (_,_,_,p2,_) -> p1 - p2) !edges;
  List.iter (fun x, y, _, p, l -> pp_hint l p) !edges;
;;
