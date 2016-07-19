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

(* $Id: nCicRefiner.mli 12479 2013-02-01 13:47:25Z fguidi $ *)

exception RefineFailure of (Stdpp.location * string) Lazy.t;;
exception Uncertain of (Stdpp.location * string) Lazy.t;;
exception AssertFailure of string Lazy.t;;

type 'a expected_type = [ `XTNone       (* unknown *)
                        | `XTSome of 'a (* the given term *) 
		        | `XTSort       (* any sort *)
		        | `XTInd        (* any (co)inductive type *)
                        ]
val typeof :
 #NCicCoercion.status ->
 ?localise:(NCic.term -> Stdpp.location) ->
  NCic.metasenv -> NCic.substitution -> NCic.context -> 
  NCic.term -> NCic.term expected_type -> (* term, expected type *)
    NCic.metasenv * NCic.substitution * NCic.term * NCic.term
    (*  menv, subst,refined term, type *)

val typeof_obj :
 #NCicCoercion.status ->
 ?localise:(NCic.term -> Stdpp.location) ->
  NCic.obj -> NCic.obj

val debug : bool ref
