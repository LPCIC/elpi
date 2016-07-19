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

(* $Id: nUri.mli 12524 2013-02-24 16:20:34Z fguidi $ *)

type uri

val string_of_uri: uri -> string
val name_of_uri: uri -> string
val baseuri_of_uri: uri -> string
val uri_of_string: string -> uri
val eq: uri -> uri -> bool
val compare: uri -> uri -> int
val hash: uri -> int

module UriHash: Hashtbl.S with type key = uri
module UriMap: Map.S with type key = uri
module UriSet: Set.S with type elt = uri
