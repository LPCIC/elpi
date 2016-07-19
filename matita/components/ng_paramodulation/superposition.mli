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

(* $Id: index.mli 9822 2009-06-03 15:37:06Z tassi $ *)

module Superposition (B : Orderings.Blob) : 
  sig

                        (* bag, maxvar, meeting point *)
    exception Success of 
      B.t Terms.bag 
      * int 
      * B.t Terms.unit_clause
      * B.t Terms.substitution

    (* The returned active set is the input one + the selected clause *)
    val infer_right :
          B.t Terms.bag -> 
          int -> (* maxvar *)
          B.t Terms.unit_clause -> (* selected passive *)
          Index.Index(B).active_set ->
            B.t Terms.bag * int * Index.Index(B).active_set * B.t Terms.unit_clause list

    val infer_left :  
          B.t Terms.bag -> 
          int -> (* maxvar *)
          B.t Terms.unit_clause -> (* selected goal *)
          Index.Index(B).active_set ->
            B.t Terms.bag * int * B.t Terms.unit_clause list

    val demodulate : 
          B.t Terms.bag ->
          B.t Terms.unit_clause ->
          Index.Index(B).DT.t -> B.t Terms.bag * B.t Terms.unit_clause

    val simplify : 
          Index.Index(B).DT.t ->
          int ->
          B.t Terms.bag ->
          B.t Terms.unit_clause ->
            B.t Terms.bag * (B.t Terms.unit_clause option)

    (* may raise success *)
    val simplify_goal :
          no_demod:bool ->
          int ->
          Index.Index(B).DT.t ->
          B.t Terms.bag ->
          B.t Terms.unit_clause list ->
          B.t Terms.unit_clause ->
            (B.t Terms.bag * B.t Terms.unit_clause) option

    val one_pass_simplification:
      B.t Terms.unit_clause ->
      Index.Index(B).active_set ->
      B.t Terms.bag ->
      int ->
      B.t Terms.bag * (B.t Terms.unit_clause * Index.Index(B).active_set) option
    val keep_simplified:
      B.t Terms.unit_clause ->
      Index.Index(B).active_set ->
      B.t Terms.bag ->
      int ->
      B.t Terms.bag * (B.t Terms.unit_clause * Index.Index(B).active_set) option

    val  orphan_murder:
      B.t Terms.bag ->
      B.t Terms.unit_clause list ->
      B.t Terms.unit_clause ->
      bool

    val are_alpha_eq : 
      B.t Terms.unit_clause ->
      B.t Terms.unit_clause ->
      bool
  end
