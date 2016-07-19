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

type mathml_markup = boxml_markup Mpresentation.mpres
and boxml_markup = mathml_markup Box.box

type markup = mathml_markup

(** {2 Markup conversions} *)

val mpres_of_box: boxml_markup -> mathml_markup
val box_of_mpres: mathml_markup -> boxml_markup

(** {2 Rendering} *)

(** level 1 -> level 0
 * @param ids_to_uris mapping id -> uri for hyperlinking
 * @param prec precedence level *)
val render:
 #NCic.status ->
 lookup_uri:(Content.id -> string option) -> ?prec:int -> NotationPt.term ->
  markup

(** level 0 -> xml stream *)
val print_xml: markup -> Xml.token Stream.t

(* |+* level 1 -> xml stream
 * @param ids_to_uris +|
val render_to_boxml:
  (Cic.id, string) Hashtbl.t -> NotationPt.term -> Xml.token Stream.t *)

val print_box:    boxml_markup -> Xml.token Stream.t
val print_mpres:  mathml_markup -> Xml.token Stream.t

