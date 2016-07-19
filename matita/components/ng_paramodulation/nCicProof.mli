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

type eq_sig_type = Eq | EqInd_l | EqInd_r | Refl

val set_default_sig: unit -> unit
val get_sig: eq_sig_type -> NCic.term

val mk_proof:
 #NCic.status ->
  ?demod:bool
  -> NCic.term Terms.bag 
  -> Terms.M.key 
  -> NCic.term Terms.substitution
  -> Terms.M.key list 
  -> NCic.term * NCic.term (* proof, type *)
