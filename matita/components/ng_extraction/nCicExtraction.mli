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

(* $Id: nCicEnvironment.mli 11172 2011-01-11 21:06:37Z sacerdot $ *)

type info
type db

class type g_status =
 object
  method extraction_db: db
 end

class virtual status :
 object ('self)
  inherit g_status
  inherit NCic.status
  method set_extraction_db: db -> 'self
  method set_extraction_status: #g_status -> 'self
 end

val empty_info: info

val refresh_uri_in_info:
 refresh_uri_in_reference:(NReference.reference -> NReference.reference) ->
  info -> info

val register_infos: db -> info -> db

(* Haskell *)
val haskell_of_obj: (#status as 'status) -> NCic.obj ->
 'status * (string * info)
