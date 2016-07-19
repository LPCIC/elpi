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

val print_tac: bool -> string -> 's NTacStatus.tactic

val dot_tac: 's NTacStatus.tactic
val branch_tac: ?force:bool -> 's NTacStatus.tactic
val shift_tac: 's NTacStatus.tactic
val pos_tac: int list -> 's NTacStatus.tactic
val case_tac: string -> 's NTacStatus.tactic
val wildcard_tac: 's NTacStatus.tactic
val merge_tac: 's NTacStatus.tactic
val focus_tac: int list -> 's NTacStatus.tactic
val unfocus_tac: 's NTacStatus.tactic
val skip_tac: 's NTacStatus.tactic
val try_tac: NTacStatus.tac_status NTacStatus.tactic -> 's NTacStatus.tactic
val repeat_tac: NTacStatus.tac_status NTacStatus.tactic -> 's NTacStatus.tactic

val compare_statuses : past:#NTacStatus.lowtac_status -> present:#NTacStatus.lowtac_status -> int list * int list

val distribute_tac:
 NTacStatus.lowtac_status NTacStatus.lowtactic -> 's NTacStatus.tactic
val exec : NTacStatus.tac_status NTacStatus.tactic -> 's NTacStatus.lowtactic
val block_tac: 's NTacStatus.tactic list -> 's NTacStatus.tactic

val apply_tac: NTacStatus.tactic_term -> 's NTacStatus.tactic
val assumption_tac: 's NTacStatus.tactic
val change_tac: 
   where:NTacStatus.tactic_pattern -> with_what:NTacStatus.tactic_term -> 
     's NTacStatus.tactic
val cut_tac: NTacStatus.tactic_term -> 's NTacStatus.tactic
val elim_tac: 
   what:NTacStatus.tactic_term -> where:NTacStatus.tactic_pattern -> 
     's NTacStatus.tactic
val intro_tac: string -> 's NTacStatus.tactic
val intros_tac: 
     ?names_ref:string list ref -> string list -> 's NTacStatus.tactic
val cases_tac: 
   what:NTacStatus.tactic_term -> where:NTacStatus.tactic_pattern -> 
     's NTacStatus.tactic
val case1_tac: string -> 's NTacStatus.tactic
val lapply_tac: NTacStatus.tactic_term -> 's NTacStatus.tactic
val rewrite_tac:
  dir:[ `LeftToRight | `RightToLeft ] ->
   what:NTacStatus.tactic_term -> where:NTacStatus.tactic_pattern -> 
    's NTacStatus.tactic
val generalize0_tac : NotationPt.term list -> 's NTacStatus.tactic
val generalize_tac : where:NTacStatus.tactic_pattern -> 's NTacStatus.tactic
val clear_tac : string list -> 's NTacStatus.tactic
val reduce_tac: 
      reduction:[ `Normalize of bool | `Whd of bool ] ->
      where:NTacStatus.tactic_pattern -> 's NTacStatus.tactic
val letin_tac: 
      where:NTacStatus.tactic_pattern ->
      what: NTacStatus.tactic_term ->
      string -> 's NTacStatus.tactic
val assert_tac:
 ((string * [`Decl of NTacStatus.tactic_term | `Def of NTacStatus.tactic_term * NTacStatus.tactic_term]) list * NTacStatus.tactic_term) list ->
  's NTacStatus.tactic

val constructor_tac : 
 ?num:int -> args:NTacStatus.tactic_term list -> 's NTacStatus.tactic

val atomic_tac : NTacStatus.tac_status NTacStatus.tactic -> 's NTacStatus.tactic
 (*(NTacStatus.tac_status -> 'c #NTacStatus.status) ->
    (#NTacStatus.tac_status as 'f) -> 'f*)

type indtyinfo 

val ref_of_indtyinfo : indtyinfo -> NReference.reference

val analyze_indty_tac :
    what:NTacStatus.tactic_term ->
    indtyinfo option ref -> (#NTacStatus.tac_status as 'a) -> 'a


val find_in_context : 'a -> ('a * 'b) list -> int

val inversion_tac: 
   what:NTacStatus.tactic_term -> where:NTacStatus.tactic_pattern -> 
     's NTacStatus.tactic
