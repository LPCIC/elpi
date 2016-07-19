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

type 'a mpres = 
  (* token elements *)
    Mi of attr * string
  | Mn of attr * string
  | Mo of attr * string
  | Mtext of attr * string
  | Mspace of attr
  | Ms of attr * string
  | Mgliph of attr * string
  (* General Layout Schemata *)
  | Mrow of attr * 'a mpres list
  | Mfrac of attr * 'a mpres * 'a mpres
  | Msqrt of attr * 'a mpres
  | Mroot of attr * 'a mpres * 'a mpres
  | Mstyle of attr * 'a mpres
  | Merror of attr * 'a mpres
  | Mpadded of attr * 'a mpres
  | Mphantom of attr * 'a mpres
  | Mfenced of attr * 'a mpres list
  | Menclose of attr * 'a mpres
  (* Script and Limit Schemata *)
  | Msub of attr * 'a mpres * 'a mpres
  | Msup of attr * 'a mpres * 'a mpres
  | Msubsup of attr * 'a mpres * 'a mpres *'a mpres 
  | Munder of attr * 'a mpres * 'a mpres
  | Mover of attr * 'a mpres * 'a mpres
  | Munderover of attr * 'a mpres * 'a mpres *'a mpres 
  (* Tables and Matrices *)
  | Mtable of attr * 'a row list
  (* Enlivening Expressions *)
  | Maction of attr * 'a mpres list
  (* Embedding *)
  | Mobject of attr * 'a

and 'a row = Mtr of attr * 'a mtd list

and 'a mtd = Mtd of attr * 'a mpres

  (** XML attribute: namespace, name, value *)
and attr = (string option * string * string) list

;;

val get_attr: 'a mpres -> attr
val set_attr: attr -> 'a mpres -> 'a mpres

val smallskip : 'a mpres 
val indented : 'a mpres -> 'a mpres
val standard_tbl_attr : attr
val two_rows_table : attr -> 'a mpres -> 'a mpres -> 'a mpres
val two_rows_table_with_brackets :
  attr -> 'a mpres -> 'a mpres -> 'a mpres -> 'a mpres
val two_rows_table_without_brackets :
  attr -> 'a mpres -> 'a mpres -> 'a mpres -> 'a mpres
val row_with_brackets :
  attr -> 'a mpres -> 'a mpres -> 'a mpres -> 'a mpres
val row_without_brackets :
  attr -> 'a mpres -> 'a mpres -> 'a mpres -> 'a mpres
val print_mpres : ('a -> Xml.token Stream.t) -> 'a mpres -> Xml.token Stream.t
val document_of_mpres : 'a mpres -> Xml.token Stream.t

