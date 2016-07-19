(* Copyright (C) 2000, HELM Team.
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

(*************************************************************************)
(*                                                                       *)
(*                           PROJECT HELM                                *)
(*                                                                       *)
(*                Andrea Asperti <asperti@cs.unibo.it>                   *)
(*                             13/2/2004                                 *)
(*                                                                       *)
(*************************************************************************)

type 
  'expr box =
    Text of attr * string
  | Space of attr
  | Ink of attr
  | H of attr * ('expr box) list
  | V of attr * ('expr box) list
  | HV of attr * ('expr box) list
  | HOV of attr * ('expr box) list
  | Object of attr * 'expr
  | Action of attr * ('expr box) list

and attr = (string option * string * string) list

val get_attr: 'a box -> attr
val set_attr: attr -> 'a box -> 'a box

val smallskip : 'expr box
val skip: 'expr box
val indent : 'expr box -> 'expr box

val box2xml:
  obj2xml:('a -> Xml.token Stream.t) -> 'a box ->
    Xml.token Stream.t

val map: ('a -> 'b) -> 'a box -> 'b box

(*
val document_of_box :
  ~obj2xml:('a -> Xml.token Stream.t) -> 'a box -> Xml.token Stream.t
*)

val b_h: attr -> 'expr box list -> 'expr box
val b_v: attr -> 'expr box list -> 'expr box
val b_hv: attr -> 'expr box list -> 'expr box  (** default indent and spacing *)
val b_hov: attr -> 'expr box list -> 'expr box (** default indent and spacing *)
val b_text: attr -> string -> 'expr box
val b_object: 'expr -> 'expr box
val b_indent: 'expr box -> 'expr box
val b_space: 'expr box
val b_kw: string -> 'expr box
val b_toggle: 'expr box list -> 'expr box (** action which toggle among items *)

val pp_attr: attr -> string

