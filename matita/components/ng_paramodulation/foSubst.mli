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

(*
module Subst (B : Terms.Blob) : 
  sig
*)
    val id_subst : 'a Terms.substitution
    val build_subst : 
      int -> 'a Terms.foterm -> 'a Terms.substitution -> 
       'a Terms.substitution
    val lookup : 
          int -> 'a Terms.substitution -> 'a Terms.foterm
    val filter : 'a Terms.substitution -> Terms.varlist -> Terms.varlist
    val reloc_subst : 
          'a Terms.substitution -> 'a Terms.foterm -> 'a Terms.foterm
    val apply_subst : 
          'a Terms.substitution -> 'a Terms.foterm -> 'a Terms.foterm
    val flat: 
          'a Terms.substitution -> 'a Terms.substitution
    val concat: 
          'a Terms.substitution -> 'a Terms.substitution -> 
            'a Terms.substitution
(*   end *)
