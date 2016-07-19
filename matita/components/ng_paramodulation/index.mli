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

(* $Id: index.mli 10591 2009-12-09 15:35:07Z asperti $ *)

module Index (B : Orderings.Blob) : 
  sig
    module ClauseSet : Set.S with 
      type elt = Terms.direction * B.t Terms.unit_clause

    module FotermIndexable : Discrimination_tree.Indexable with 
      type constant_name = B.t and
      type input = B.t Terms.foterm 

    module DT : Discrimination_tree.DiscriminationTree with 
      type constant_name = B.t and 
      type input = B.t Terms.foterm and 
      type data = ClauseSet.elt and 
      type dataset = ClauseSet.t
    
    val index_unit_clause : 
      DT.t -> B.t Terms.unit_clause -> DT.t 

    val remove_unit_clause :
      DT.t -> B.t Terms.unit_clause -> DT.t 

    val fold : 
      DT.t ->
      (B.t Discrimination_tree.path -> ClauseSet.t -> 'a -> 'a) 
      -> 'a -> 'a

    val elems : DT.t -> ClauseSet.t

    type active_set = B.t Terms.unit_clause list * DT.t

  end
