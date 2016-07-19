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

(* $Id: utf8Macro.ml 8749 2008-06-23 15:06:12Z tassi $ *)

exception Macro_not_found of string
exception Utf8_not_found of string

let expand macro =
  try
    Hashtbl.find Utf8MacroTable.macro2utf8 macro
  with Not_found -> raise (Macro_not_found macro)

let unicode_of_tex s =
  try
    if s.[0] = '\\' then
      expand (String.sub s 1 (String.length s - 1))
    else s
  with Macro_not_found _ -> s

let tex_of_unicode s =
 (*WARNING: the space below is a nbsp (0x00A0), not a normal space *)
 if s = " " then [""]
 else
  try
    let alt = 
      List.map (fun x -> "\\"^x) 
       (Hashtbl.find_all Utf8MacroTable.utf82macro s)
    in
    List.sort 
      (fun x y -> Pervasives.compare (String.length x) (String.length y)) 
      alt
  with Not_found -> []

let pp_table () =
  let rec list_uniq ?(eq=(=)) = function 
    | [] -> []
    | h::[] -> [h]
    | h1::h2::tl when eq h1 h2 -> list_uniq ~eq (h2 :: tl) 
    | h1::tl (* when h1 <> h2 *) -> h1 :: list_uniq ~eq tl
  in
  let l = ref [] in
  Hashtbl.iter (fun k _ -> l := k :: !l) Utf8MacroTable.utf82macro;
  l := list_uniq (List.sort compare !l);
  List.map 
    (fun k -> 
       let vs = Hashtbl.find_all Utf8MacroTable.utf82macro k in
       (k, List.map (fun x -> "\\"^x) vs))
    !l
;;
