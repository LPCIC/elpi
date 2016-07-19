(* Copyright (C) 2004-2005, HELM Team.
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

(* $Id: matitaTypes.ml 11131 2010-12-19 20:28:10Z sacerdot $ *)

open Printf
open GrafiteTypes

  (** user hit the cancel button *)
exception Cancel

type abouts =
  [ `Blank
  | `Current_proof
  | `Us
  | `Coercions
  | `CoercionsFull
  | `TeX
  | `Grammar
  | `Hints
  ]
  
type mathViewer_entry =
  [ `About of abouts  (* current proof *)
  | `Check of string  (* term *)
  | `NCic of NCic.term * NCic.context * NCic.metasenv * NCic.substitution
  | `Dir of string  (* "directory" in cic uris namespace *)
  | `NRef of NReference.reference (* cic object uri *)
  ]

let string_of_entry = function
  | `About `Blank -> "about:blank"
  | `About `Current_proof -> "about:proof"
  | `About `Us -> "about:us"
  | `About `Coercions -> "about:coercions?tred=true"
  | `About `CoercionsFull -> "about:coercions"
  | `About `TeX -> "about:tex"
  | `About `Grammar -> "about:grammar"
  | `About `Hints -> "about:hints"
  | `Check _ -> "check:"
  | `NCic (_, _, _, _) -> "nterm:"
  | `Dir uri -> uri
  | `NRef nref -> NReference.string_of_reference nref

let entry_of_string = function
  | "about:blank" -> `About `Blank
  | "about:proof" -> `About `Current_proof
  | "about:us"    -> `About `Us
  | "about:hints"    -> `About `Hints
  | "about:coercions?tred=true"    -> `About `Coercions
  | "about:coercions"    -> `About `CoercionsFull
  | "about:tex"    -> `About `TeX
  | "about:grammar"    -> `About `Grammar
  | _ ->  (* only about entries supported ATM *)
      raise (Invalid_argument "entry_of_string")
