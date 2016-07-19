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

class type g_status =
 object
  inherit NCicUnifHint.g_status
  method coerc_db: db
 end

class virtual status :
 object ('self)
  inherit g_status
  inherit NCicUnifHint.status
  method set_coerc_db: db -> 'self
  method set_coercion_status: #g_status -> 'self
 end

val empty_db: db

(* index (\x.c ?? x ??): A -> B
   index_coercion db c A B \arity_left(c ??x??) \position(x,??x??) 
*)
val index_coercion: 
  #status as 'status -> string ->
   NCic.term -> NCic.term -> NCic.term -> int -> int -> 'status

(* NOTE: the name of the coercion is used to sort coercions, thus 
 * two coercions matching the same number of symbols are sorted 
 * according to their name *)
val look_for_coercion:
    #status ->
    NCic.metasenv -> NCic.substitution -> NCic.context -> 
    (* inferred type, expected type *)
    NCic.term -> NCic.term -> 
      (* name, enriched metasenv, new term, its type, metavriable to
       * be unified with the old term *)
      (string * NCic.metasenv * NCic.term * NCic.term * NCic.term) list

(* returns (coercion,arity,arg) *)
val match_coercion:
 #status -> metasenv:NCic.metasenv -> subst:NCic.substitution ->
  context:NCic.context -> NCic.term -> (NCic.term * int * int) option

val generate_dot_file: #status -> Format.formatter -> unit
