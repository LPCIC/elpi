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

(* $Id: nCicPp.mli 11172 2011-01-11 21:06:37Z sacerdot $ *)

val r2s: #NCic.status -> bool -> NReference.reference -> string

val string_of_flavour: NCic.def_flavour -> string

(* low-level pretty printer;
   all methods are meant to be overridden in ApplyTransformation *)
class status: NCic.cstatus

(* variants that use a formatter 
module Format : sig
  val ppterm: 
    formatter:Format.formatter ->
    context:NCic.context -> 
    subst:NCic.substitution -> 
    metasenv:NCic.metasenv ->
    ?margin:int ->
    ?inside_fix:bool ->
     NCic.term -> unit
  
  val ppcontext:
    ?sep:string ->
    formatter:Format.formatter ->
    subst:NCic.substitution -> 
    metasenv:NCic.metasenv ->
    NCic.context -> unit 
  
  val ppmetasenv:
    formatter:Format.formatter ->
    subst:NCic.substitution -> NCic.metasenv -> unit
  
  val ppsubst: 
    formatter:Format.formatter ->
    metasenv:NCic.metasenv -> NCic.substitution -> unit
  
  val ppobj: 
    formatter:Format.formatter -> NCic.obj -> unit
end
*)
