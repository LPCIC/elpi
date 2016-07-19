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

(* $Id: nUri.ml 12524 2013-02-24 16:20:34Z fguidi $ *)

type uri = int * string (* shareno, URI *)

let string_of_uri (_, uri) = uri;;

let name_of_uri (_, uri) = 
  let name = Filename.basename uri in
  Filename.chop_extension name
;;

let baseuri_of_uri (_,uri) =
 Filename.dirname uri
;;

module OrderedStrings =
 struct
  type t = string
  let compare (s1 : t) (s2 : t) = compare s1 s2
 end
;;

module MapStringsToUri = Map.Make(OrderedStrings);;

let set_of_uri = ref MapStringsToUri.empty;;

let uri_of_string = 
  let counter = ref 0 in 
  let c () = incr counter; !counter in 
fun s ->
  try MapStringsToUri.find s !set_of_uri
  with Not_found ->
    let new_uri = c(), s in
    set_of_uri := MapStringsToUri.add s new_uri !set_of_uri;
    new_uri
;;

let eq = (==);;
let compare (n1,_) (n2,_) = n2 - n1;;
let hash (n,_) = n;;

module HT = struct
        type t = uri
        let equal = eq
        let compare = compare
        let hash = hash;;
end;;

module UriHash = Hashtbl.Make(HT);;
module UriMap = Map.Make(HT);;
module UriSet = Set.Make(HT);;
