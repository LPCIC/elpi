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

(* $Id: nReference.ml 12051 2012-05-17 11:32:52Z sacerdot $ *)

exception IllFormedReference of string Lazy.t

type spec = 
 | Decl 
 | Def of int (* height *)
 | Fix of int * int * int (* fixno, recparamno, height *)
 | CoFix of int
 | Ind of bool * int * int (* inductive, indtyno, leftno *)
 | Con of int * int * int  (* indtyno, constrno, leftno  *)

type reference = Ref of NUri.uri * spec

let eq = (==);;

let compare (Ref (u1,s1)) (Ref (u2,s2)) =
 let res = NUri.compare u1 u2 in
  if res = 0 then compare s1 s2 else res
;;

let hash (Ref (uri,spec)) =
 Hashtbl.hash spec + NUri.hash uri
;;

module OrderedStrings =
 struct
  type t = string
  let compare (s1 : t) (s2 : t) = Pervasives.compare s1 s2
 end
;;

module MapStringsToReference = Map.Make(OrderedStrings);;

let set_of_reference = ref MapStringsToReference.empty;;

(* Note: valid ELPI constant
 * '+' not allowed in path and name
 *
 * Decl                   cic:/path/name+dec
 * Def                    cic:/path/name+def<i>
 * Fix of int * int       cic:/path/name+fix<i/j/h>
 * CoFix of int           cic:/path/name+cfx<i>
 * Ind of int             cic:/path/name+ind<b/i/l>
 * Con of int * int       cic:/path/name+con<i/j/l>
 *)

let uri_suffix_of_ref_suffix = function
    | "dec" | "fix" | "cfx" | "def" -> "con"
    | "ind" | "con" -> "ind"
    | x -> prerr_endline (x ^ " not a valid suffix"); assert false
;;

let reference_of_string =
  let get3 s dot =
    let comma2 = String.rindex s '/' in
    let comma = String.rindex_from s (comma2-1) '/' in
    let s_i = String.sub s (dot+5) (comma-dot-5) in
    let s_j = String.sub s (comma+1) (comma2-comma-1) in
    let s_h = String.sub s (comma2+1) (String.length s-comma2-2) in
    let i = int_of_string s_i in
    let j = int_of_string s_j in
    let h = int_of_string s_h in
    i,j,h
  in
(*
  let get2 s dot =
    let comma = String.rindex s ',' in
    let i = int_of_string (String.sub s (dot+5) (comma-dot-5)) in
    let j = int_of_string (String.sub s (comma+1) (String.length s-comma-2)) in
    i,j
  in
*)
  let get1 s dot =
    let i = int_of_string (String.sub s (dot+5) (String.length s-1-dot-5)) in
    i
  in
fun s ->
  try MapStringsToReference.find s !set_of_reference
  with Not_found ->
    let new_reference =
      try
        let dot = String.rindex s '+' in
        let prefix = String.sub s 0 (dot+1) in
        let suffix = String.sub s (dot+1) 3 in
        let u = NUri.uri_of_string (prefix ^ uri_suffix_of_ref_suffix suffix) in
        match suffix with
        | "dec" -> Ref (u, Decl)
        | "def" -> let i = get1 s dot in Ref (u, Def i)
        | "fix" -> let i,j,h = get3 s dot in Ref (u, Fix (i,j,h))
        | "cfx" -> let i = get1 s dot in Ref (u, CoFix (i))
        | "ind" -> let b,i,l = get3 s dot in Ref (u, Ind (b=1,i,l))
        | "con" -> let i,j,l = get3 s dot in Ref (u, Con (i,j,l))
        | _ -> raise Not_found
      with Not_found -> raise (IllFormedReference (lazy s))
    in
    set_of_reference := MapStringsToReference.add s new_reference !set_of_reference;
    new_reference
;;

let string_of_reference (Ref (u,indinfo)) =
  let s = NUri.string_of_uri u in
  let dot = String.rindex s '+' in
  let s2 = String.sub s 0 dot in
  match indinfo with
  | Decl ->  s2 ^ "+dec"
  | Def h -> s2 ^ "+def<" ^ string_of_int h ^ ">"
  | Fix (i,j,h)  -> 
      s2 ^ "+fix<" ^ string_of_int i ^ "/" ^
      string_of_int j ^ "/" ^ string_of_int h ^ ">"
  | CoFix i -> s2 ^ "+cfx<" ^ string_of_int i ^ ">"
  | Ind (b,i,l)->s2 ^"+ind<" ^(if b then "1" else "0")^ "/" ^ string_of_int i ^
      "/" ^ string_of_int l ^ ">"
  | Con (i,j,l) -> s2 ^ "+con<" ^ string_of_int i ^ "/" ^ string_of_int j ^
      "/" ^ string_of_int l ^ ">"
;;

let mk_constructor j = function
  | Ref (u, Ind (_,i,l)) -> 
      reference_of_string (string_of_reference (Ref (u, Con (i,j,l))))
  | r -> 
      raise (IllFormedReference (lazy ("NON INDUCTIVE TYPE REFERENCE: " ^
        string_of_reference r))); 
;;
let mk_indty b = function
  | Ref (u, Con (i,_,l)) -> 
      reference_of_string (string_of_reference (Ref (u, Ind (b,i,l))))
  | r -> 
      raise (IllFormedReference (lazy 
        ("NON INDUCTIVE TYPE CONSTRUCTOR REFERENCE: " ^ string_of_reference r))); 
;;

let mk_fix i j = function
  | Ref (u, Fix (_,_,h)) -> 
      reference_of_string (string_of_reference (Ref (u, Fix (i,j,h))))
  | _ -> assert false
;;

let mk_cofix i = function
  | Ref (u, CoFix _) -> 
      reference_of_string (string_of_reference (Ref (u, CoFix i)))
  | _ -> assert false
;;

let reference_of_spec u spec = 
  reference_of_string (string_of_reference (Ref (u, spec)))
;;
