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

(* $Id: nCic.ml 9058 2008-10-13 17:42:30Z tassi $ *)

let string_of_comparison = function
  | Terms.Lt -> "=<="
  | Terms.Gt -> "=>="
  | Terms.Eq -> "==="
  | Terms.Incomparable -> "=?="
  | Terms.Invertible -> "=<->="

module Pp (B : Terms.Blob) = struct

(* Main pretty printing functions *)

let pp_foterm ~formatter:f t =
  let rec aux ?(toplevel=false) = function
    | Terms.Leaf x ->
	Format.fprintf f "%s" (B.pp x)
    | Terms.Var i ->
	Format.fprintf f "?%d" i
    | Terms.Node (hd::tl) ->
	Format.fprintf f "@[<hov 2>";
	if not toplevel then Format.fprintf f "(";
	aux hd;
	List.iter (fun x -> Format.fprintf f "@;";
		     aux x) tl;
	if not toplevel then Format.fprintf f ")";
	Format.fprintf f "@]"
    | _ ->
	assert false
  in
    aux ~toplevel:true t
;;

let string_of_rule = function
  | Terms.Superposition -> "Super"
  | Terms.Demodulation ->  "Demod"
;;

let string_of_direction = function
    | Terms.Left2Right -> "Left to right"
    | Terms.Right2Left -> "Right to left"
    | Terms.Nodir -> "No direction"
;;

let pp_substitution ~formatter:f subst =
  Format.fprintf f "@[<v 2>";
  List.iter
    (fun (i, t) ->
       (Format.fprintf f "?%d -> " i;
	pp_foterm f t;
	Format.fprintf f "@;"))
    subst;
  Format.fprintf f "@]";
;;

let pp_proof bag ~formatter:f p =
  let rec aux eq = function
    | Terms.Exact t -> 
        Format.fprintf f "%d: Exact (" eq;
        pp_foterm f t;
        Format.fprintf f ")@;";
    | Terms.Step (rule,eq1,eq2,dir,pos,subst) ->
        Format.fprintf f "%d: %s("
          eq (string_of_rule rule);
	Format.fprintf f "|%d with %d dir %s))" eq1 eq2
	  (string_of_direction dir);
	let (_, _, _, proof1),_,_ = Terms.get_from_bag eq1 bag in
	let (_, _, _, proof2),_,_ = Terms.get_from_bag eq2 bag in
	  Format.fprintf f "@[<v 2>";
          aux eq1 proof1;	    
          aux eq2 proof2;
	  Format.fprintf f "@]";
  in
    Format.fprintf f "@[<v>";
    aux 0 p;
    Format.fprintf f "@]"
;;

let pp_unit_clause ~formatter:f c =
  let (id, l, vars, proof) = c in
    Format.fprintf f "Id : %3d, " id ;
    match l with
      | Terms.Predicate t ->
	  Format.fprintf f "@[<hv>{";
	  pp_foterm f t;
          Format.fprintf f "@;[%s] by "
            (String.concat ", " (List.map string_of_int vars));
          (match proof with
           | Terms.Exact t -> pp_foterm f t
           | Terms.Step (rule, id1, id2, _, p, _) -> 
               Format.fprintf f "%s %d with %d at %s" 
                 (string_of_rule rule) id1 id2 (String.concat
                  "," (List.map string_of_int p)));
          Format.fprintf f "@]"
      | Terms.Equation (lhs, rhs, ty, comp) ->
	  Format.fprintf f "@[<hv>{";
	  pp_foterm f ty;
          Format.fprintf f "}:@;@[<hv>";
	  pp_foterm f lhs;
          Format.fprintf f "@;%s@;" (string_of_comparison comp);
	  pp_foterm f rhs;
          Format.fprintf f "@]@;[%s] by "
            (String.concat ", " (List.map string_of_int vars));
          (match proof with
           | Terms.Exact t -> pp_foterm f t
           | Terms.Step (rule, id1, id2, _, p, _) -> 
               Format.fprintf f "%s %d with %d at %s" 
                 (string_of_rule rule) id1 id2 (String.concat
                  "," (List.map string_of_int p)));
          Format.fprintf f "@]"
;;

let pp_bag ~formatter:f (_,bag) = 
  Format.fprintf f "@[<v>";
  Terms.M.iter 
  (fun _ (c,d,_) -> pp_unit_clause ~formatter:f c;
     if d then Format.fprintf f " (discarded)@;"
     else Format.fprintf f "@;") bag;
  Format.fprintf f "@]"
;;

(* String buffer implementation *)
let on_buffer ?(margin=80) f t = 
  let buff = Buffer.create 100 in
  let formatter = Format.formatter_of_buffer buff in
  Format.pp_set_margin formatter margin;
  f ~formatter:formatter t;
  Format.fprintf formatter "@?";
  Buffer.contents buff
;;

let pp_bag =
  on_buffer pp_bag
;;

let pp_foterm =
 on_buffer pp_foterm
;;

let pp_substitution =
  on_buffer pp_substitution
;;

let pp_proof bag =
  on_buffer (pp_proof bag)
;;

let pp_unit_clause ?margin x=
  on_buffer ?margin pp_unit_clause x
;;

end
