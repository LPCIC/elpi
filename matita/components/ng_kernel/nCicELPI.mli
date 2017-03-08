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

type outcome = private Skip of string
             |         Fail
             |         OK

(* use this kernel: valid values "NO" (default), "CSC", "FG0", "FG1" *)
val set_kernel_from_string: string -> unit

(* turn trace facility on *)
val trace_on: unit -> unit

(* turn informational prints off *)
val prints_off: unit -> unit

(* turn cache on *)
val cache_on: unit -> unit

(* actions to take at exit, if any *)
val at_exit: unit -> unit

(* is_type r u is OK if the type of u is a sort *)
val is_type: NReference.reference -> NCic.term -> outcome

(* has_type r t u is OK if the type of t is u *)
val has_type: NReference.reference -> NCic.term -> NCic.term -> outcome

(* approx s c r t v w is OK if v of inferred type w refines t in context c and subst s *)
val approx: NReference.reference -> NCic.substitution -> NCic.context -> NCic.term -> NCic.term -> NCic.term -> outcome

(* approx_cast r s c t u v is OK if v refines t of expected type u in context c and subst s *)
val approx_cast: NReference.reference -> NCic.substitution -> NCic.context -> NCic.term -> NCic.term -> NCic.term -> outcome
