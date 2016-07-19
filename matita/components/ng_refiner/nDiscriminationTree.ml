(* Copyright (C) 2005, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://cs.unibo.it/helm/.
 *)

(* $Id: nDiscriminationTree.ml 11675 2011-11-17 23:14:26Z tassi $ *)

open Discrimination_tree

module TermOT : Set.OrderedType with type t = NCic.term = struct 
  type t = NCic.term 
  let compare = Pervasives.compare 
end

module TermSet = Set.Make(TermOT)

module TermListOT : Set.OrderedType with type t = NCic.term list =
 struct
   type t = NCic.term list
   let compare = Pervasives.compare
 end

module TermListSet : Set.S with type elt = NCic.term list =
 Set.Make(TermListOT)


module NCicIndexable : Indexable
with type input = NCic.term 
and type constant_name = NReference.reference = struct

type input = NCic.term
type constant_name = NReference.reference

let ppelem = function
  | Constant (ref,arity) -> 
      "("^NReference.string_of_reference ref ^ "," ^ string_of_int arity^")"
  | Bound (i,arity) -> 
      "("^string_of_int i ^ "," ^ string_of_int arity^")"
  | Variable -> "?"
  | Proposition -> "Prop"
  | Datatype -> "Type"
  | Dead -> "Dead"
;;

let path_string_of t =
  let rec aux arity depth = function
    | NCic.Appl ((NCic.Meta _|NCic.Implicit _)::_) -> [Variable]
    | NCic.Appl (NCic.Match _::_) -> [Dead]
    | NCic.Appl (NCic.Lambda _ :: _) -> [Variable] (* maybe we should b-reduce *)
    | NCic.Appl [] -> assert false
    | NCic.Appl l when depth > 10 || List.length l > 50 -> [Variable]
    | NCic.Appl (hd::tl) ->
       aux (List.length tl) depth hd @ 
       List.flatten (List.map (aux 0 (depth+1)) tl)
    | NCic.Lambda _ -> [Variable]
        (* I think we should CicSubstitution.subst Implicit t *)
    | NCic.LetIn _ -> [Variable] (* z-reduce? *)
    | NCic.Meta _ | NCic.Implicit _ -> assert (arity = 0); [Variable]
    | NCic.Rel i -> [Bound (i, arity)]
    | NCic.Sort (NCic.Prop) -> assert (arity=0); [Proposition]
    | NCic.Sort _ -> assert (arity=0); [Datatype]
    | NCic.Const (u) -> [Constant (u, arity)]
    (* Prod is used for coercions to funclass, ?->?       *)
    (*  so it should not be unifiable with any other term *)
    | NCic.Match _ | NCic.Prod _ -> [Dead] 
  in 
  aux 0 0 t
;;

let compare e1 e2 =
  match e1,e2 with
  | Constant (u1,a1),Constant (u2,a2) -> 
       let x = NReference.compare u1 u2 in
       if x = 0 then Pervasives.compare a1 a2 else x
  | e1,e2 -> Pervasives.compare e1 e2
;;

let string_of_path l = String.concat "." (List.map ppelem l) ;;

end

module DiscriminationTree = Make(NCicIndexable)(TermSet)
