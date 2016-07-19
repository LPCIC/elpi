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

(* $Id: nReference.mli 12051 2012-05-17 11:32:52Z sacerdot $ *)

exception IllFormedReference of string Lazy.t

type spec = 
 | Decl 
 | Def of int              (* height *)
 | Fix of int * int * int  (* fixno, recparamno, height *)
 | CoFix of int
 | Ind of bool * int * int (* inductive, indtyno, leftno *)
 | Con of int * int * int  (* indtyno, constrno, leftno  *)

type reference = private Ref of NUri.uri * spec

val reference_of_spec: NUri.uri -> spec -> reference

val eq: reference -> reference -> bool
val compare: reference -> reference -> int
val hash: reference -> int
val string_of_reference: reference -> string 
val reference_of_string: string -> reference

(* given the reference of an inductive type, returns the i-th contructor *)
val mk_constructor: int -> reference -> reference
(* given the reference of an inductive type constructor, returns the indty *)
val mk_indty: bool -> reference -> reference
val mk_fix: int -> int -> reference -> reference
val mk_cofix: int -> reference -> reference
