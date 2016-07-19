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


(* evals a coercion declaration statement: name compose t ty (id,src) tgt *)
val eval_ncoercion: 
   #GrafiteTypes.status as 'status ->
     string ->
     bool ->
     NotationPt.term ->
     NotationPt.term ->
     string * NotationPt.term ->
     NotationPt.term -> 'status * NUri.uri list

(* for records, the term is the projection, already refined, while the
 * first integer is the number of left params and the second integer is 
 * the arity in the `:arity>` syntax *)
val basic_eval_and_record_ncoercion_from_t_cpos_arity: 
   #GrafiteTypes.status as 'status ->
     string * bool * NCic.term * int * int -> 'status * NUri.uri list

