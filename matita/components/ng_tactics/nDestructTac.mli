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

val destruct_tac : string list option -> string list -> 's NTacStatus.tactic

val mk_discriminator: (use_jmeq: bool) -> ?force:bool ->
  string -> NCic.inductiveType -> int ->  
  (#NTacStatus.tac_status as 's) -> string -> 's * NCic.obj

exception ConstructorTooBig of string

