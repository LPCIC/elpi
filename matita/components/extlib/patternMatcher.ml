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
 * http://helm.cs.unibo.it/
 *)

(* $Id: patternMatcher.ml 11503 2011-09-26 12:24:20Z sacerdot $ *)

open Printf

type pattern_kind = Variable | Constructor
type tag_t = int

type pattern_id = int

module OrderedInt =
struct
  type t = int
  let compare (x1:t) (x2:t) = Pervasives.compare x2 x1  (* reverse order *)
end

module IntSet = Set.Make (OrderedInt)

let int_set_of_int_list l =
  List.fold_left (fun acc i -> IntSet.add i acc) IntSet.empty l

module type PATTERN =
sig
  type pattern_t
  type term_t
  val classify : pattern_t -> pattern_kind
  val tag_of_pattern : pattern_t -> tag_t * pattern_t list
  val tag_of_term : term_t -> tag_t * term_t list
  val string_of_term: term_t -> string
  val string_of_pattern: pattern_t -> string
end

module Matcher (P: PATTERN) =
struct
  type row_t = P.pattern_t list * P.pattern_t list * pattern_id
  type t = row_t list

  let compatible p1 p2 = P.classify p1 = P.classify p2

  let matched = List.map (fun (matched, _, pid) -> matched, pid)

  let partition t pidl =
    let partitions = Hashtbl.create 11 in
    let add pid row = Hashtbl.add partitions pid row in
    (try
      List.iter2 add pidl t
    with Invalid_argument _ -> assert false);
    let pidset = int_set_of_int_list pidl in
    IntSet.fold
      (fun pid acc ->
        match Hashtbl.find_all partitions pid with
        | [] -> acc
        | patterns -> (pid, List.rev patterns) :: acc)
      pidset []

  let are_empty t =
    match t with
    | (_, [], _) :: _ -> true
      (* if first row has an empty list of patterns, then others have as well *)
    | _ -> false

    (* return 2 lists of rows, first one containing homogeneous rows according
     * to "compatible" below *)
  let horizontal_split t =
    let ap, first_row, t', first_row_class =
      match t with
      | [] -> assert false
      | (_, [], _) :: _ ->
          assert false  (* are_empty should have been invoked in advance *)
      | ((_, hd :: _ , _) as row) :: tl -> hd, row, tl, P.classify hd
    in
    let rec aux prev_t = function
      | [] -> List.rev prev_t, []
      | (_, [], _) :: _ -> assert false
      | ((_, hd :: _, _) as row) :: tl when compatible ap hd ->
          aux (row :: prev_t) tl
      | t -> List.rev prev_t, t
    in
    let rows1, rows2 = aux [first_row] t' in
    first_row_class, rows1, rows2

    (* return 2 lists, first one representing first column, second one
     * representing a new pattern matrix where matched patterns have been moved
     * to decl *)
  let vertical_split t =
    List.map
      (function
        | decls, hd :: tl, pid -> hd :: decls, tl, pid
        | _ -> assert false)
      t

  let variable_closure ksucc kfail =
    (fun matched_terms constructors terms ->
(* prerr_endline "variable_closure"; *)
      match terms with
      | hd :: tl -> ksucc (hd :: matched_terms) constructors tl
      | _ -> kfail () (*CSC: was assert false, but it did happen*))

  let success_closure ksucc =
    (fun matched_terms constructors terms ->
(* prerr_endline "success_closure"; *)
       ksucc matched_terms constructors)

  let constructor_closure ksuccs =
    (fun matched_terms constructors terms ->
(* prerr_endline "constructor_closure"; *)
      match terms with
      | t :: tl ->
          (try
            let tag, subterms = P.tag_of_term t in
            let constructors' =
              if subterms = [] then t :: constructors else constructors
            in
            let k' = List.assoc tag ksuccs in
            k' matched_terms constructors' (subterms @ tl)
          with Not_found -> None)
      | [] -> assert false)

  let backtrack_closure ksucc kfail =
    (fun matched_terms constructors terms ->
(* prerr_endline "backtrack_closure"; *)
      match ksucc matched_terms constructors terms with
      | Some x -> Some x
      | None -> kfail matched_terms constructors terms)

  let compiler rows match_cb fail_k =
    let rec aux t =
      if t = [] then
        (fun _ _ _ -> fail_k ())
      else if are_empty t then
        success_closure (match_cb (matched t))
      else
        match horizontal_split t with
        | _, [], _ -> assert false
        | Variable, t', [] -> variable_closure (aux (vertical_split t')) fail_k
        | Constructor, t', [] ->
            let tagl =
              List.map
                (function
                  | _, p :: _, _ -> fst (P.tag_of_pattern p)
                  | _ -> assert false)
                t'
            in
            let clusters = partition t' tagl in
            let ksuccs =
              List.map
                (fun (tag, cluster) ->
                  let cluster' =
                    List.map  (* add args as patterns heads *)
                      (function
                        | matched_p, p :: tl, pid ->
                            let _, subpatterns = P.tag_of_pattern p in
                            matched_p, subpatterns @ tl, pid
                        | _ -> assert false)
                      cluster
                  in
                  tag, aux cluster')
                clusters
            in
            constructor_closure ksuccs
        | _, t', t'' -> backtrack_closure (aux t') (aux t'')
    in
    let t = List.map (fun (p, pid) -> [], [p], pid) rows in
    let matcher = aux t in
    (fun term -> matcher [] [] [term])
end

