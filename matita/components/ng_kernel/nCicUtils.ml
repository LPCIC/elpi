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

(* $Id: nCicUtils.ml 11172 2011-01-11 21:06:37Z sacerdot $ *)

module C = NCic
module Ref = NReference

exception Subst_not_found of int
exception Meta_not_found of int

let head_beta_reduce = ref (fun _ ~upto:_ _ -> assert false);;
let set_head_beta_reduce = (:=) head_beta_reduce;;

let expand_local_context = function
  | C.Irl len -> 
      let rec aux acc = function 
        | 0 -> acc
        | n -> aux (C.Rel n::acc) (n-1)
      in
       aux [] len
  | C.Ctx lctx -> lctx
;;

let lookup_subst n subst =
  try
    List.assoc n subst
  with Not_found -> raise (Subst_not_found n)
;;

let lookup_meta n metasenv =
  try
    List.assoc n metasenv
  with Not_found -> raise (Meta_not_found n)
;;

let fold g k f acc = function
 | C.Meta _ -> assert false
 | C.Implicit _
 | C.Sort _
 | C.Const _
 | C.Rel _ -> acc
 | C.Appl [] | C.Appl [_] -> assert false
 | C.Appl l -> List.fold_left (f k) acc l
 | C.Prod (n,s,t)
 | C.Lambda (n,s,t) -> f (g (n,C.Decl s) k) (f k acc s) t
 | C.LetIn (n,ty,t,bo) -> f (g (n,C.Def (t,ty)) k) (f k (f k acc ty) t) bo
 | C.Match (_,oty,t,pl) -> List.fold_left (f k) (f k (f k acc oty) t) pl
;;

let map status g k f = function
 | C.Meta _ -> assert false
 | C.Implicit _
 | C.Sort _
 | C.Const _
 | C.Rel _ as t -> t
 | C.Appl [] | C.Appl [_] -> assert false
 | C.Appl l as orig ->
    let fire_beta, upto = 
      match l with C.Meta _ :: _ -> true, List.length l - 1 | _ -> false, 0 
    in
    let l1 = HExtlib.sharing_map (f k) l in
    if l == l1 then orig else
    let t =
      match l1 with
      | C.Appl l :: tl -> C.Appl (l@tl)
      | l1 -> C.Appl l1
    in
      if fire_beta then !head_beta_reduce (status :> NCic.status) ~upto t
      else t
 | C.Prod (n,s,t) as orig ->
     let s1 = f k s in let t1 = f (g (n,C.Decl s) k) t in
     if t1 == t && s1 == s then orig else C.Prod (n,s1,t1)
 | C.Lambda (n,s,t) as orig -> 
     let s1 = f k s in let t1 = f (g (n,C.Decl s) k) t in
     if t1 == t && s1 == s then orig else C.Lambda (n,s1,t1)
 | C.LetIn (n,ty,t,b) as orig -> 
     let ty1 = f k ty in let t1 = f k t in
     let b1 = f (g (n,C.Def (t,ty)) k) b in
     if ty1 == ty && t1 == t && b1 == b then orig else C.LetIn (n,ty1,t1,b1)
 | C.Match (r,oty,t,pl) as orig -> 
     let oty1 = f k oty in let t1 = f k t in let pl1 = HExtlib.sharing_map (f k) pl in
     if oty1 == oty && t1 == t && pl1 == pl then orig 
     else C.Match(r,oty1,t1,pl1)
;;
