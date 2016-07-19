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

(* $Id: terms.ml 9836 2009-06-05 15:33:35Z denes $ *)

val lexicograph : ('a -> 'b -> int) -> 'a list -> 'b list -> int

module Utils (B : Orderings.Blob) :
  sig
    val eq_foterm : B.t Terms.foterm -> B.t Terms.foterm -> bool
    val compare_foterm : B.t Terms.foterm -> B.t Terms.foterm -> int

    val eq_literal : B.t Terms.literal -> B.t Terms.literal -> bool
    val compare_literal : B.t Terms.literal -> B.t Terms.literal -> int

    (* mk_unit_clause [maxvar] [type] [proof] -> [clause] * [maxvar] *)
    val mk_unit_clause : 
         int -> B.t Terms.foterm -> B.t Terms.foterm -> 
           B.t Terms.unit_clause * int

    val mk_passive_clause :
      B.t Terms.unit_clause -> B.t Terms.passive_clause

    val mk_passive_goal :
      B.t Terms.unit_clause -> B.t Terms.passive_clause

    val eq_unit_clause : B.t Terms.unit_clause -> B.t Terms.unit_clause -> bool
    val compare_unit_clause : B.t Terms.unit_clause -> B.t Terms.unit_clause -> int


    val fresh_unit_clause : 
          int -> B.t Terms.unit_clause -> B.t Terms.unit_clause * int

    (* relocate [maxvar] [varlist] -> [newmaxvar] * [varlist] * [relocsubst] *)
    val relocate : 
          int -> int list -> B.t Terms.substitution -> 
            int * int list * B.t Terms.substitution 

    val compare_passive_clauses_weight :
      B.t Terms.passive_clause -> B.t Terms.passive_clause -> int

    val compare_passive_clauses_age :
      B.t Terms.passive_clause -> B.t Terms.passive_clause -> int

  end
