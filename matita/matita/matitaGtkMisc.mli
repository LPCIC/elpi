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

(** {2 Gtk helpers} *)

  (** given a window and a check menu item it links the two so that the former
   * is only hidden on delete and the latter toggle show/hide of the former *)
val toggle_window_visibility:
  window:GWindow.window -> check:GMenu.check_menu_item -> unit
  
  (** given a window and a check menu item it links the two so that the former
   * is only hidden on delete and the latter toggle show/hide of the former *)
val toggle_widget_visibility:
  widget:GObj.widget -> check:GMenu.check_menu_item -> unit

val toggle_callback:
  callback:(bool -> unit) -> check:GMenu.check_menu_item -> unit
  
val toggle_win:
  ?check:GMenu.check_menu_item -> GWindow.window -> unit -> unit

(** Connect a callback to the clicked signal of a button, ignoring its return
  * value *)
val connect_button: #GButton.button -> (unit -> unit) -> unit


(** Connect a callback to the toggled signal of a button, ignoring its return
  * value *)
val connect_toggle_button: #GButton.toggle_button -> (unit -> unit) -> unit

(** Like connect_button above, but connects a callback to the activate signal of
  * a menu item *)
val connect_menu_item: #GMenu.menu_item -> (unit -> unit) -> unit

  (** connect a unit -> unit callback to a particular key press event. Event can
  * be specified using its keysym and a list of modifiers which must be in
  * effect for the callback to be executed. Further signal processing of other
  * key press events remains unchanged; further signal processing of the
  * specified key press depends on the stop parameter *)
val connect_key:
  GObj.event_ops ->
  ?modifiers:Gdk.Tags.modifier list ->
  ?stop:bool ->     (* stop signal handling when the given key has been pressed?
                     * Defaults to false *)
  Gdk.keysym ->     (* (= int) the key, see GdkKeysyms.ml *)
  (unit -> unit) -> (* callback *)
    unit

  (** n-ary string column list *)
class multiStringListModel:
  cols:int ->
  GTree.view ->
  object
    method list_store: GTree.list_store (** list_store forwarding *)

    method easy_mappend:     string list -> unit        (** append + set *)
    method easy_minsert:     int -> string list -> unit (** insert + set *)
    method easy_mselection:  unit -> string list list
  end
  
  (** single string column list *)
class stringListModel:
  GTree.view ->
  object
    inherit multiStringListModel

    method easy_append:     string -> unit        (** append + set *)
    method easy_insert:     int -> string -> unit (** insert + set *)
    method easy_selection:  unit -> string list
  end
  

  (** as above with Pixbuf associated to each row. Each time an insert is
   * performed a string tag should be specified, the corresponding pixbuf in the
   * tags associative list will be shown on the left of the inserted row *)
class taggedStringListModel:
  tags:((string * GdkPixbuf.pixbuf) list) ->
  GTree.view ->
  object
    method list_store: GTree.list_store (** list_store forwarding *)

    method easy_append:     tag:string -> string -> unit
    method easy_insert:     int -> tag:string -> string -> unit
    method easy_selection:  unit -> string list
  end

(** {2 Matita GUI components} *)

class type gui =
  object  (* minimal gui object requirements *)
    method newUriDialog:          unit -> MatitaGeneratedGui.uriChoiceDialog
    method newConfirmationDialog: unit -> MatitaGeneratedGui.confirmationDialog
    method newEmptyDialog:        unit -> MatitaGeneratedGui.emptyDialog
  end

  (** {3 Dialogs}
   * In functions below:
   * @param title window title
   * @param message content of the text label shown to the user *)

  (** @param parent to center the window on it *)
val ask_confirmation:
  title:string -> message:string -> 
  ?parent:#GWindow.window_skel ->
  unit ->
    [`YES | `NO | `CANCEL]

  (** @param multiline (default: false) if true a TextView widget will be used
  * for prompting the user otherwise a TextEntry widget will be
  * @return the string given by the user *)
val ask_text:
  gui:#gui ->
  ?title:string -> ?message:string ->
  ?multiline:bool -> ?default:string -> unit ->
    string

val report_error:
  title:string -> message:string -> 
  ?parent:#GWindow.window_skel ->
  unit ->
    unit

    (* given an utf8 string a floc returns the parsed substring and its length
     * in bytes *)
val utf8_parsed_text: string -> Stdpp.location -> string * int

    (* the length in characters, not bytes *)
val utf8_string_length: string -> int

val escape_pango_markup: string -> string

val matita_lang: GSourceView2.source_language
