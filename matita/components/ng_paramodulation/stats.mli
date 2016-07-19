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

(* $Id: stats.mli 9822 2009-06-03 15:37:06Z denes $ *)

module Stats (B : Orderings.Blob) : 
  sig

    module SymbMap : Map.S with type key = B.t

    val parse_symbols : B.t Terms.unit_clause list -> (* hypotheses *)
                       B.t Terms.unit_clause -> (* goal *)
                       (B.t * int * int * int * int list) list

    val dependencies : B.t -> B.t Terms.unit_clause list -> B.t list


  end
