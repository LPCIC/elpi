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

(* $Id: renderingAttrs.ml 5881 2006-01-20 12:47:16Z asperti $ *)

type xml_attribute = string option * string * string
type markup = [ `MathML | `BoxML ]

let color1 = "blue"
(* let color2 = "red" *)
let color2 = "blue"

let keyword_attributes = function
  | `MathML -> [ None, "mathcolor", color1 ]
  | `BoxML -> [ None, "color", color1 ]

let builtin_symbol_attributes = function
  | `MathML -> [ None, "mathcolor", color1 ]
  | `BoxML -> [ None, "color", color1 ]

let object_keyword_attributes = function
  | `MathML -> [ None, "mathcolor", color2 ]
  | `BoxML -> [ None, "color", color2 ]

let symbol_attributes _ = []
let ident_attributes _ = []
let number_attributes _ = []

let spacing_attributes _ = [ None, "spacing", "0.5em" ]
let indent_attributes _ = [ None, "indent", "0.5em" ]
let small_skip_attributes _ = [ None, "width", "0.5em" ]

