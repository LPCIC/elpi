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

(* $Id: disambiguateChoices.ml 11076 2010-11-18 10:44:56Z asperti $ *)

open Printf

open DisambiguateTypes

exception Choice_not_found of string Lazy.t

let has_description dsc = (fun x -> fst x = dsc)

let nlookup_num_by_dsc dsc =
 if dsc <> "natural number" then
  raise (Choice_not_found (lazy ("Num with dsc " ^  dsc)))
 else
  "natural number", `Num_interp Nnumber_notation.ninterp_natural_number

let mk_choice  ~mk_appl ~mk_implicit ~term_of_nref (dsc, args, appl_pattern)=
  dsc,
  `Sym_interp
  (fun cic_args ->
    let env',rest =
      let names =
        List.map (function NotationPt.IdentArg (_, name) -> name) args
      in
       let rec combine_with_rest l1 l2 =
        match l1,l2 with
           _::_,[] -> raise (Invalid_argument "combine_with_rest")
         | [],rest -> [],rest
         | he1::tl1,he2::tl2 ->
            let l,rest = combine_with_rest tl1 tl2 in
             (he1,he2)::l,rest
       in
        try
         combine_with_rest names cic_args
        with Invalid_argument _ ->
         raise (Invalid_choice (lazy (Stdpp.dummy_loc, 
           "The notation " ^ dsc ^ " expects more arguments")))
    in
     let combined =
      Interpretations.instantiate_appl_pattern 
        ~mk_appl ~mk_implicit ~term_of_nref env' appl_pattern
     in
      match rest with
         [] -> combined
       | _::_ -> mk_appl (combined::rest))

let lookup_symbol_by_dsc status ~mk_appl ~mk_implicit ~term_of_nref symbol dsc =
  let interpretations =
   Interpretations.lookup_interpretations status ~sorted:false symbol in
  try
    mk_choice ~mk_appl ~mk_implicit ~term_of_nref
      (List.find (fun (dsc', _, _) -> dsc = dsc') interpretations)
  with Interpretations.Interpretation_not_found | Not_found ->
    raise (Choice_not_found (lazy (sprintf "Symbol %s, dsc %s" symbol dsc)))
