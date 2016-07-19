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

val absolute_path: string -> string 

  (** @return true if file is a (textual) proof script *)
val is_proof_script: string -> bool

  (** @return true if file is a (binary) proof object *)
val is_proof_object: string -> bool

  (** given a phrase, if it doesn't end with BuildTimeConf.phrase_sep, append
  * it *)
val append_phrase_sep: string -> string

val normalize_dir: string -> string (** add trailing "/" if missing *)
val strip_suffix: suffix:string -> string -> string

  (** @return tl tail of a list starting at a given element
   * @param eq equality to be used, defaults to physical equality (==)
   * @raise Not_found *)
val list_tl_at: ?equality:('a -> 'a -> bool) -> 'a -> 'a list -> 'a list

exception History_failure

type 'a memento

class type ['a] history =
  object ('b)
    method add : 'a -> unit
    method next : 'a        (** @raise History_failure *)
    method previous : 'a    (** @raise History_failure *)
    method load: 'a memento -> unit
    method save: 'a memento
    method is_begin: bool 
    method is_end: bool 
  end

  (** shell like history: new items added at the end of the history
  * @param size maximum history size *)
class shell_history : int -> [string] history

  (** browser like history: new items added at the current point of the history
  * @param size maximum history size
  * @param first element in history (this history is never empty) *)
class ['a] browser_history: ?memento:'a memento -> int -> 'a -> ['a] history

  (** create a singleton from a given function. Given function is invoked the
  * first time it gets called. Next invocation will return first value *)
val singleton: (unit -> 'a) -> (unit -> 'a)

  (** given the base name of an image, returns its full path *)
val image_path: string -> string

  (** 2>/dev/null, HLog = (fun _ -> ()) *)
val shutup: unit -> unit

  (** outputs the preamble of a generated .ma file *)
val out_preamble: out_channel -> unit

val left_button: int
val right_button: int

(** {2 Global changes} *)

val observe_font_size: (int -> unit) -> unit
val get_current_font_size: unit -> int
val increase_font_size: unit -> unit
val decrease_font_size: unit -> unit
val reset_font_size: unit -> unit

(** CSC: these functions should completely disappear (bad design) *)
val set_gui: MatitaGuiTypes.gui -> unit
val get_gui: unit -> MatitaGuiTypes.gui
