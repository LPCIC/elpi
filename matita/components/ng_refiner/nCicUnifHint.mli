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

(* $Id: nCicRefiner.mli 9227 2008-11-21 16:00:06Z tassi $ *)

type db

exception HintNotValid

class type g_status =
 object
  method uhint_db: db
 end

class virtual status :
 object ('self)
  inherit g_status
  inherit NCic.status
  method set_uhint_db: db -> 'self
  method set_unifhint_status: #g_status -> 'self
 end

val index_hint: 
  #status as 'status -> NCic.context -> NCic.term -> NCic.term -> int -> 'status

val add_user_provided_hint :
  #status as 'status -> NCic.term -> int -> 'status

val look_for_hint:
    #status ->
    NCic.metasenv -> NCic.substitution -> NCic.context -> 
    NCic.term -> NCic.term -> 
      (NCic.metasenv * 
        (NCic.term * NCic.term) * (NCic.term * NCic.term) list) list

val eq_class_of:
      #status -> NCic.term -> NCic.term list

val generate_dot_file: #status -> Format.formatter -> unit
