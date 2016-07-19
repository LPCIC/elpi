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

(* $Id: terms.mli 9822 2009-06-03 15:37:06Z tassi $ *)

val set_eqP: NCic.term -> unit
val set_default_eqP: unit -> unit

module type NCicContext = 
  sig
    val metasenv : NCic.metasenv
    val subst : NCic.substitution
    val context : NCic.context
  end

module NCicBlob(C : NCicContext) : Terms.Blob 
with type t = NCic.term and type input = NCic.term

