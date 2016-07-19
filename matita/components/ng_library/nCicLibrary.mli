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

(* $Id: nCicLibrary.mli 13176 2016-04-18 15:29:33Z fguidi $ *)

exception LibraryOutOfSync of string Lazy.t
exception IncludedFileNotCompiled of string * string 

type timestamp

class virtual status :
 object ('self)
  inherit NCic.status
  method timestamp: timestamp
  method set_timestamp: timestamp -> 'self
  (*CSC: bug here, we are not copying the NCicExtraction and OCamlExtraction part of the status *)
 end

(* it also checks it and add it to the environment *)
val add_obj: #status as 'status -> NCic.obj -> 'status
val add_constraint: 
  #status as 'status -> acyclic:bool ->
  NCic.universe -> NCic.universe -> 'status
val aliases_of: NUri.uri -> NReference.reference list
val resolve: string -> NReference.reference list
(*
(* warning: get_obj may raise (NCicEnvironment.ObjectNotFoud l) *)
val get_obj: #NCic.status -> NUri.uri -> NCic.obj (* changes the current timestamp *)
*)

val time_travel: #status -> unit
val replace: #status -> unit

val init: unit -> unit

type obj
type dump

class type g_dumpable_status =
 object
  method dump: dump
 end

class dumpable_status :
 object ('self)
  inherit g_dumpable_status
  method set_dump: dump -> 'self
  method set_dumpable_status: #g_dumpable_status -> 'self
 end

val get_transitively_included: #dumpable_status -> NUri.uri list
val dump_obj: #dumpable_status as 'status -> obj -> 'status

module type SerializerType =
 sig
  type dumpable_status

  type 'a register_type =
   'a ->
    refresh_uri_in_universe:(NCic.universe -> NCic.universe) ->
    refresh_uri_in_term:(NCic.status -> NCic.term -> NCic.term) ->
    refresh_uri_in_reference:(NReference.reference -> NReference.reference) ->
    alias_only:bool ->
     dumpable_status -> dumpable_status

  val register: < run: 'a.  string -> 'a register_type -> ('a -> obj) >
  val serialize: baseuri:NUri.uri -> dumpable_status -> unit
  val require: baseuri:
   NUri.uri -> fname:string -> alias_only:bool ->
    dumpable_status -> dumpable_status
  val dependencies_of: baseuri:NUri.uri -> string list
 end

module Serializer(D: sig type dumpable_s = private #dumpable_status end) :
  SerializerType with type dumpable_status = D.dumpable_s

val refresh_uri: NUri.uri -> NUri.uri

val ng_path_of_baseuri: ?no_suffix:bool -> NUri.uri -> string
(* EOF *)
