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

val is_a_fact_obj: 
  #NTacStatus.pstatus -> NUri.uri -> bool

val fast_eq_check_tac:
  params:(NTacStatus.tactic_term list option * (string * string) list) -> 
   's NTacStatus.tactic

val paramod_tac:
  params:(NTacStatus.tactic_term list option * (string * string) list) -> 
   's NTacStatus.tactic

val demod_tac:
  params:(NTacStatus.tactic_term list option* (string * string) list) -> 
   's NTacStatus.tactic

val smart_apply_tac: 
  NTacStatus.tactic_term -> 's NTacStatus.tactic

val auto_tac:
  params:(NTacStatus.tactic_term list option * (string * string) list) -> 
   ?trace_ref:NotationPt.term list ref -> 
   's NTacStatus.tactic

val keys_of_type: 
  (#NTacStatus.pstatus as 'a) ->
  NTacStatus.cic_term -> 'a * NTacStatus.cic_term list

