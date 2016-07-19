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

(* $Id: index.ml 11696 2011-11-21 09:42:44Z asperti $ *)

module Index(B : Orderings.Blob) = struct
  module U = FoUtils.Utils(B)
  module Unif = FoUnif.Founif(B)
  module Pp = Pp.Pp(B)

  module ClauseOT =
    struct 
      type t = Terms.direction * B.t Terms.unit_clause
 
      let compare (d1,uc1) (d2,uc2) = 
        let c = Pervasives.compare d1 d2 in
        if c <> 0 then c else U.compare_unit_clause uc1 uc2
      ;;
    end

  module ClauseSet : 
    Set.S with type elt = Terms.direction * B.t Terms.unit_clause
    = Set.Make(ClauseOT)

  open Discrimination_tree

  module FotermIndexable : Indexable with
    type constant_name = B.t and
    type input = B.t Terms.foterm 
  =
    struct

      type input = B.t Terms.foterm
      type constant_name = B.t

      let path_string_of =
        let rec aux arity = function
          | Terms.Leaf a -> [Constant (a, arity)]
          | Terms.Var i -> (* assert (arity = 0); *) [Variable]
	  (* FIXME : should this be allowed or not ? 
          | Terms.Node (Terms.Var _::_) ->
	      assert false *)
          | Terms.Node ([] | [ _ ] ) -> assert false
          (* FIXME : if we can have a variable we can also have a term 
            | Terms.Node (Terms.Node _::_) as t -> assert false	 *)      
          | Terms.Node (hd::tl) ->
              aux (List.length tl) hd @ List.flatten (List.map (aux 0) tl) 
        in 
          aux 0
      ;;

      let compare e1 e2 = 
        match e1,e2 with 
        | Constant (a1,ar1), Constant (a2,ar2) ->
            let c = B.compare a1 a2 in
            if c <> 0 then c else Pervasives.compare ar1 ar2
        | Variable, Variable -> 0
        | Constant _, Variable -> ~-1
        | Variable, Constant _ -> 1
        | Proposition, _ | _, Proposition
        | Datatype, _ | _, Datatype
        | Dead, _ | _, Dead
        | Bound _, _ | _, Bound _ -> assert false
      ;;

      let string_of_path l = String.concat "." (List.map (fun _ -> "*") l) ;;

    end

    module DT : DiscriminationTree with
      type constant_name = B.t and 
      type input = B.t Terms.foterm and 
      type data = ClauseSet.elt and 
      type dataset = ClauseSet.t
    = Make(FotermIndexable)(ClauseSet)
  
  let process op t = function
    | (_,Terms.Equation (l,_,_,Terms.Gt),_,_) as c -> 
        op t l (Terms.Left2Right, c)
    | (_,Terms.Equation (_,r,_,Terms.Lt),_,_) as c -> 
        op t r (Terms.Right2Left, c)
    | (_,Terms.Equation (l,r,_,Terms.Incomparable),vl,_) as c ->
        op (op t l (Terms.Left2Right, c))
          r (Terms.Right2Left, c)
    | (_,Terms.Equation (l,r,_,Terms.Invertible),vl,_) as c ->
	op t l (Terms.Left2Right, c)
    | (_,Terms.Equation (_,r,_,Terms.Eq),_,_)  -> assert false
    | (_,Terms.Predicate p,_,_) as c ->
        op t p (Terms.Nodir, c)
  ;;

  let index_unit_clause = 
    process DT.index 
 
  let remove_unit_clause =
    process DT.remove_index 

  let fold = DT.fold 

  let elems index =
    DT.fold index (fun _ dataset acc -> ClauseSet.union dataset acc)
      ClauseSet.empty
    
  type active_set = B.t Terms.unit_clause list * DT.t

end
