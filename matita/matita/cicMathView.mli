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

type document_element

class type cicMathView =
object
  inherit GObj.widget

  method load_root : root:document_element -> unit
  method remove_selections: unit
  method set_selection: document_element option -> unit
  method get_selections: document_element list

    (** @raise Failure "no selection" *)
  method strings_of_selection: (MatitaGuiTypes.paste_kind * string) list

    (** set hyperlink callback. None disable hyperlink handling *)
  method set_href_callback: (string -> unit) option -> unit

    (** load a sequent and render it into parent widget *)
  method nload_sequent:
   #ApplyTransformation.status -> NCic.metasenv -> NCic.substitution -> int -> unit

  method load_nobject: #ApplyTransformation.status -> NCic.obj -> unit
end

val cicMathView :
 ?width:int ->
 ?height:int ->
 ?packing:(GObj.widget -> unit) ->
 ?show:bool -> unit ->
  cicMathView

val empty_mathml: document_element Lazy.t
val closed_goal_mathml: document_element Lazy.t

val screenshot: 
 GrafiteTypes.status -> NCic.metasenv -> NCic.metasenv ->
  NCic.substitution -> string -> unit

(* CSC: these functions should completely disappear; bad design;
   the object type is MatitaScript.script *)
val register_matita_script_current: (unit -> < advance: ?statement:string -> unit -> unit; status: GrafiteTypes.status >) -> unit
val get_matita_script_current: unit -> < advance: ?statement:string -> unit -> unit; status: GrafiteTypes.status >
