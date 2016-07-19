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

module type Blob =
  sig 
    include Terms.Blob 

    (* This order relation should be:
     * - stable for instantiation
     * - total on ground terms
     *
     *)
    val compare_terms : 
          t Terms.foterm -> t Terms.foterm -> Terms.comparison

    (* these could be outside the module, but to ease experimentation
     * we allow them to be tied with the ordering *)
    val compute_unit_clause_weight : 't Terms.unit_clause -> int
    val compute_goal_weight : 't Terms.unit_clause -> int

    val name : string

  end

module NRKBO (B : Terms.Blob) : Blob 
with type t = B.t and type input = B.input

module KBO (B : Terms.Blob) : Blob 
with type t = B.t and type input = B.input

module LPO (B : Terms.Blob) : Blob 
with type t = B.t and type input = B.input
