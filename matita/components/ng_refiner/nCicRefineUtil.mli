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

(* $Id: nCicRefiner.ml 9802 2009-05-25 15:39:26Z tassi $ *)

val alpha_equivalence : #NCic.status -> NCic.term -> NCic.term -> bool 

val replace_lifting :
  #NCic.status ->
  equality:((string * NCic.context_entry) list ->
            NCic.term -> NCic.term -> bool) ->
  context:(string * NCic.context_entry) list ->
  what:NCic.term list ->
  with_what:NCic.term list -> where:NCic.term -> NCic.term

