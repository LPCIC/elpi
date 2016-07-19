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

(* $Id: nCicEnvironment.mli 13176 2016-04-18 15:29:33Z fguidi $ *)

exception CircularDependency of string Lazy.t;;
exception ObjectNotFound of string Lazy.t;;
exception BadDependency of string Lazy.t * exn;;
exception AlreadyDefined of string Lazy.t;;

val set_get_obj: (NCic.status -> NUri.uri -> NCic.obj) -> unit

val get_checked_obj: #NCic.status -> NUri.uri -> NCic.obj

val check_and_add_obj: #NCic.status -> NCic.obj -> unit

val get_relevance: #NCic.status -> NReference.reference -> bool list

val get_checked_decl:
  #NCic.status -> NReference.reference -> 
    NCic.relevance * string * NCic.term * NCic.c_attr * int

val get_checked_def:
  #NCic.status -> NReference.reference -> 
    NCic.relevance * string * NCic.term * NCic.term * NCic.c_attr * int

(* the last integer is the index of the inductive type in the reference *)
val get_checked_indtys:
  #NCic.status -> NReference.reference -> 
    bool * int * NCic.inductiveType list * NCic.i_attr * int

val get_checked_fixes_or_cofixes:
  #NCic.status -> NReference.reference -> 
   NCic.inductiveFun list * NCic.f_attr * int

val invalidate_item: 
      [ `Obj of NUri.uri * NCic.obj 
      | `Constr of NCic.universe * NCic.universe ] -> unit

val invalidate: unit -> unit

val set_typecheck_obj: (NCic.status -> NCic.obj -> unit) -> unit

(* =========== universes ============= *)

(* utils *)
val ppsort : Format.formatter -> NCic.sort -> unit
val pp_constraints: unit -> string
val get_universes: unit -> NCic.universe list

(* use to type products *)
val max: NCic.universe -> NCic.universe -> NCic.universe

(* raise BadConstraints if the second arg. is an inferred universe or
 * if the added constraint gives circularity *)
exception BadConstraint of string Lazy.t;;
val add_lt_constraint: acyclic:bool -> NCic.universe -> NCic.universe -> unit
val universe_eq: NCic.universe -> NCic.universe -> bool
val universe_leq: NCic.universe -> NCic.universe -> bool
val universe_lt: NCic.universe -> NCic.universe -> bool

(* checks if s1 <= s2 *)
val are_sorts_convertible: test_eq_only:bool -> NCic.sort -> NCic.sort -> bool

(* to type a Match *)
val allowed_sort_elimination: NCic.sort -> NCic.sort -> [ `Yes | `UnitOnly ]

(* algebraic successor function *)
exception UntypableSort of string Lazy.t
exception AssertFailure of string Lazy.t
val typeof_sort: NCic.sort -> NCic.sort

(* looks for a declared universe that is the least one above the input *)
val sup : NCic.universe -> NCic.universe option
val inf : strict:bool -> NCic.universe -> NCic.universe option
val family_of : NCic.universe -> [ `CProp | `Type ]

(* =========== /universes ============= *)

(* EOF *)
