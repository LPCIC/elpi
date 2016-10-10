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

(* has_some_sort u is false (?) if the type of u is a sort *)
val has_some_sort: NReference.reference -> NCic.term -> bool

(* has_type t u is false (?) if the type of t is u *)
val has_type: NReference.reference -> NCic.term -> NCic.term -> bool
