(* Copyright (C) 2004, HELM Team.
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

(* $Id: number_notation.ml 9771 2009-05-14 13:43:55Z fguidi $ *)

let error msg =
   raise (DisambiguateTypes.Invalid_choice (lazy (Stdpp.dummy_loc, msg)))

let build_nat o s str =
   let n = int_of_string str in
   if n < 0 then error (str ^ " is not a valid natural number number") else
   let rec aux n = if n = 0 then o () else s (aux (pred n)) in
   aux n

let ninterp_natural_number num =
  (*
   let nat_URI = match Obj.nat_URI () with
      | Some uri -> uri
      | None     -> error "no default natural numbers"
   in
  *)
   let nat_URI = NUri.uri_of_string "cic:/matita/arithmetics/nat/nat.ind" in
   let o () =
    NCic.Const
     (NReference.reference_of_spec nat_URI (NReference.Con (0,1,0))) in
   let s t =
    NCic.Appl
     [NCic.Const
      (NReference.reference_of_spec nat_URI (NReference.Con (0,2,0)));
      t] in
   build_nat o s num
