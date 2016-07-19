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

let debug s = prerr_endline (Lazy.force s);;
let debug _ = ();;

let convert_term = ref (fun _ _ -> assert false);;
let set_convert_term f = convert_term := f;;

module COT : Set.OrderedType 
with type t = string * NCic.term * int * int  * NCic.term * NCic.term = 
  struct
     type t = string * NCic.term * int * int * NCic.term * NCic.term
     let compare = Pervasives.compare
  end

module CoercionSet = Set.Make(COT)

module DB = 
  Discrimination_tree.Make(NDiscriminationTree.NCicIndexable)(CoercionSet)

type db = DB.t * DB.t

let empty_db = DB.empty,DB.empty

class type g_status =
 object
  inherit NCicUnifHint.g_status
  method coerc_db: db
 end

class virtual status =
 object
  inherit NCicUnifHint.status
  val db = empty_db
  method coerc_db = db
  method set_coerc_db v = {< db = v >}
  method set_coercion_status
   : 'status. #g_status as 'status -> 'self
   = fun o -> {< db = o#coerc_db >}#set_unifhint_status o
 end

let index_coercion (status:#status) name c src tgt arity arg =
  let db_src,db_tgt = status#coerc_db in
  let data = (name,c,arity,arg,src,tgt) in
  debug (lazy ("INDEX:" ^ 
    status#ppterm ~metasenv:[] ~subst:[] ~context:[] src ^ " ===> " ^
    status#ppterm ~metasenv:[] ~subst:[] ~context:[] tgt ^ "  :=  " ^
    status#ppterm ~metasenv:[] ~subst:[] ~context:[] c ^ " " ^ 
    string_of_int arg ^ " " ^ string_of_int arity));
  let db_src = DB.index db_src src data in
  let db_tgt = DB.index db_tgt tgt data in
  status#set_coerc_db (db_src, db_tgt)
;;

let look_for_coercion status metasenv subst context infty expty =
 let db_src,db_tgt = status#coerc_db in
  match 
    NCicUntrusted.apply_subst status subst context infty, 
    NCicUntrusted.apply_subst status subst context expty 
  with
  | (NCic.Meta _ | NCic.Appl (NCic.Meta _::_)), 
    (NCic.Meta _ | NCic.Appl (NCic.Meta _::_)) -> [] 
  | infty, expty ->

    debug (lazy ("LOOK FOR COERCIONS: " ^ 
      status#ppterm ~metasenv ~subst ~context infty ^ "  |===> " ^
      status#ppterm ~metasenv ~subst ~context expty));

    let src_class = infty :: NCicUnifHint.eq_class_of status infty in
    let tgt_class = expty :: NCicUnifHint.eq_class_of status expty in

    let set_src = 
      List.fold_left 
        (fun set infty -> 
          DB.Collector.union (DB.retrieve_unifiables_sorted db_src infty) set)
        DB.Collector.empty src_class
    in
    let set_tgt = 
      List.fold_left 
        (fun set expty -> 
          DB.Collector.union (DB.retrieve_unifiables_sorted db_tgt expty) set)
        DB.Collector.empty tgt_class
    in

    debug (lazy ("CANDIDATES SRC: " ^ 
      String.concat "," (List.map (fun (name,t,_,_,_,_) ->
        name ^ " :: " ^ status#ppterm ~metasenv ~subst ~context t) 
      (DB.Collector.to_list set_src))));
    debug (lazy ("CANDIDATES TGT: " ^ 
      String.concat "," (List.map (fun (name,t,_,_,_,_) ->
        name ^ " :: " ^ status#ppterm ~metasenv ~subst ~context t) 
      (DB.Collector.to_list set_tgt))));

    let candidates = DB.Collector.inter set_src set_tgt in

    debug (lazy ("CANDIDATES: " ^ 
      String.concat "," (List.map (fun (name,t,_,_,_,_) ->
        name ^ " :: " ^ status#ppterm ~metasenv ~subst ~context t) 
      candidates)));

    List.map
      (fun (name,t,arity,arg,_,_) ->
          let ty =
            try NCicTypeChecker.typeof status ~metasenv:[] ~subst:[] [] t 
            with NCicTypeChecker.TypeCheckerFailure s ->
             prerr_endline ("illtyped coercion: "^Lazy.force s);
             prerr_endline (status#ppterm ~metasenv:[] ~subst:[] ~context:[] t);
             assert false
          in
          let ty, metasenv, args = 
           NCicMetaSubst.saturate status ~delta:max_int metasenv subst context ty arity
          in

          debug (lazy (
            status#ppterm ~metasenv ~subst:[] ~context:[] ty ^ " --- " ^ 
            status#ppterm ~metasenv ~subst ~context
            (NCicUntrusted.mk_appl t args) ^ " --- " ^ 
              string_of_int (List.length args) ^ " == " ^ string_of_int arg)); 
             
          name,metasenv, NCicUntrusted.mk_appl t args, ty, List.nth args arg)
      candidates
;;

(* CSC: very inefficient implementation!
   Enrico, can we use a discrimination tree here? *)
let match_coercion status ~metasenv ~subst ~context t =
 let db =
  DB.fold (fst (status#coerc_db)) (fun _ v l -> (CoercionSet.elements v)@l) []
 in
    (HExtlib.list_findopt
      (fun (_,p,arity,cpos,_,_) _ ->
        try
         let t =
          match p,t with
             NCic.Appl lp, NCic.Appl lt ->
              (match fst (HExtlib.split_nth (List.length lp) lt) with
                  [t] -> t
                | l -> NCic.Appl l)
           | _,NCic.Appl (he::_) -> he
           | _,_ -> t
         in
         let b = NCicReduction.alpha_eq status metasenv subst context p t in
         if not b then None else
         let ty = NCicTypeChecker.typeof status ~metasenv:[] ~subst:[] [] p in
         let pis = 
           let rec aux = function NCic.Prod (_,_,t) -> 1+aux t | _ -> 0 in
           aux ty
         in
         Some (p,pis - arity - cpos - 1,cpos)
        with
         Failure _ -> None (* raised by split_nth *)
      ) db)
;;

let generate_dot_file (status:#status) fmt =
  let module Pp = GraphvizPp.Dot in
  let src_db, _ = status#coerc_db in
  let edges = ref [] in
  DB.iter src_db (fun _ dataset -> 
     edges := !edges @ 
      List.map
        (fun (name,t,a,g,sk,dk) -> 
          debug(lazy (let p = status#ppterm ~metasenv:[] ~context:[]
                ~subst:[] in p t ^ " ::: " ^ p sk ^ " |--> " ^ p dk));
          let eq_s= sk::NCicUnifHint.eq_class_of status sk in
          let eq_t= dk::NCicUnifHint.eq_class_of status dk in
          (name,t,a,g),eq_s,eq_t
          )
        (CoercionSet.elements dataset);
    );
  let nodes = 
    HExtlib.list_uniq
     (List.sort compare 
       (List.flatten
         (List.map
           (fun (_,a,b) ->
             [a;b]
            )
           !edges)))
  in
  let names = ref [] in
  let id = ref 0 in
  let mangle l =
    try List.assoc l !names
    with Not_found ->
      incr id;
      names := (l,"node"^string_of_int!id) :: !names;
      List.assoc l !names
  in
  List.iter 
    (fun cl -> 
      Pp.node (mangle cl) 
      ~attrs:["label",String.concat "\\n"
        (List.map (fun t->
          status#ppterm ~metasenv:[] ~subst:[]
           ~context:[] t ~margin:max_int
        ) cl)]
      fmt)
    nodes;
  List.iter 
    (fun ((name,_,_,_),src,tgt) ->
       Pp.edge (mangle src) (mangle tgt)
       ~attrs:["label", name] fmt)
    !edges;
;;
