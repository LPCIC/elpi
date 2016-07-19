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

(** {2 Optional values} *)

val map_option: ('a -> 'b) -> 'a option -> 'b option
val iter_option: ('a -> unit) -> 'a option -> unit
val unopt: 'a option -> 'a  (** @raise Failure *)

(** {2 Filesystem} *)

val is_dir: string -> bool  (** @return true if file is a directory *)
val writable_dir: string -> bool  (** @return true if the directory is writable *)
val is_regular: string -> bool  (** @return true if file is a regular file *)
val is_executable: string -> bool  (** @return true if file is executable *)
val mkdir: string -> unit (** create dir and parents. @raise Failure *)
val tilde_expand: string -> string  (** bash-like (head) tilde expansion *)
val safe_remove: string -> unit (** removes a file if it exists *)
val safe_rmdir: string -> unit (** removes a dir if it exists and is empty *)
val is_dir_empty: string -> bool (** checks if the dir is empty *)
val rmdir_descend: string -> unit (** rmdir -p *)
val chmod: int -> string -> unit (** chmod *)
val normalize_path: string -> string (** /foo/./bar/..//baz -> /foo/baz *)

  (** find all _files_ whose name matches test under a filesystem root.
   * Test is passed the filename path relative to the given filesystem root *)
val find: ?test:(string -> bool) -> string -> string list 

  (** find_in paths name returns the first path^"/"^name such that 
   *  is a regular file and the current user can 'stat' it. 
   *  May raise (Failure "find_in") *)
val find_in: string list -> string -> string

(** {2 File I/O} *)

val input_file: string -> string  (** read all the contents of file to string *)
val input_all: in_channel -> string (** read all the contents of a channel *)
val output_file: filename:string -> text:string -> unit (** other way round *)

(** {2 Exception handling} *)

  (** @param finalizer finalization function (execution both in case of success
   * and in case of raised exception
   * @param f function to be invoked
   * @param arg argument to be passed to function *)
val finally: (unit -> unit) -> ('a -> 'b) -> 'a -> 'b

(** {2 Char processing} *)

val is_alpha: char -> bool
val is_blank: char -> bool
val is_digit: char -> bool
val is_alphanum: char -> bool (** is_alpha || is_digit *)

(** {2 String processing} *)

val split: ?sep:char -> string -> string list (** @param sep defaults to ' ' *)
val trim_blanks: string -> string (** strip heading and trailing blanks *)

(** {2 List processing} *)

val list_uniq: 
  ?eq:('a->'a->bool) -> 'a list -> 'a list (** uniq unix filter on lists *)
val filter_map: ('a -> 'b option) -> 'a list -> 'b list (** filter + map *)
val filter_map_acc: ('acc -> 'a -> ('acc * 'b) option) -> 'acc -> 'a list ->
        'acc * 'b list (** fold/filter + map *)
val filter_map_monad: ('acc -> 'a -> 'acc * 'b option) -> 'acc -> 'a list ->
        'acc * 'b list (** fold/filter + map *)

val list_rev_map_filter: ('a -> 'b option) -> 'a list -> 'b list
val list_rev_map_filter_fold: ('c -> 'a -> 'c * 'b option) -> 'c -> 'a list -> 'c * 'b list
val list_concat: ?sep:'a list -> 'a list list -> 'a list (**String.concat-like*)
val list_iter_sep: sep:(unit -> unit) -> ('a -> unit) -> 'a list -> unit
val list_findopt: ('a -> int -> 'b option) -> 'a list -> 'b option
val flatten_map: ('a -> 'b list) -> 'a list -> 'b list
val list_last: 'a list -> 'a
val list_mapi: ('a -> int -> 'b) -> 'a list -> 'b list
val list_mapi_acc: 
      ('a -> int -> 'acc -> 'acc * 'b) -> 'acc -> 'a list -> 'acc * 'b list 
(* Finds the zero based index of the first element that satisfies a predicate*)
val list_index: ('a -> bool) -> 'a list -> (int * 'a) option
val sharing_map: ('a -> 'a) -> 'a list -> 'a list
val sharing_map_acc: 
     ('acc -> 'a -> 'acc * 'a) -> 'acc -> 'a list -> 'acc * 'a list
(* Iters in parallel on two lists until the first list is empty.
   The second one can be shorter and is padded with a default value.
   This function cannot fail. *)
val list_iter_default2: ('a -> 'b -> unit) -> 'a list -> 'b -> 'b list -> unit
exception FailureAt of int
(* Checks a predicate in parallel on three lists, the first two having the same
   length (otherwise it raises Invalid_argument). It stops when the first two
   lists are empty. The third one can be shorter and is padded with a default
   value. It can also raise FailureAt when ??? *)
val list_forall_default3: ('a -> 'b -> 'c -> bool) -> 'a list -> 'b list -> 'c -> 'c list -> bool
val list_forall_default3_var: ('a -> 'b -> 'c -> bool) -> 'a list -> 'b list -> 'c -> 'c list -> bool

  (** split_nth n l
   * @returns two list, the first contains at least n elements, the second the
   * remaining ones
   * @raise Failure when List.length l < n *)
val split_nth: int -> 'a list -> 'a list * 'a list

 (** skip [n] [l] skips the first n elements of l *)
val list_skip : int -> 'a list -> 'a list

val mk_list: 'a -> int -> 'a list

(* makes the list [start; ...; stop - 1] *)
val list_seq: int -> int -> int list

(* like List.assoc but returns all bindings *)
val list_assoc_all: 'a -> ('a * 'b) list -> 'b list

val rm_assoc_option : 'a -> ('a * 'b) list -> 'b option * ('a * 'b) list

val rm_assoc_assert : 'a -> ('a * 'b) list -> 'b * ('a * 'b) list

val clusters : (int -> int list) -> int list -> int list list
(** {2 Debugging & Profiling} *)

type profiler = { profile : 'a 'b. ('a -> 'b) -> 'a -> 'b }

  (** @return a profiling function; [s] is used for labelling the total time at
   * the end of the execution *)
val profile : ?enable:bool -> string -> profiler
val set_profiling_printings : (string -> bool) -> unit

(** {2 Localized exceptions } *)

exception Localized of Stdpp.location * exn

val loc_of_floc: Stdpp.location -> int * int
val floc_of_loc: int * int -> Stdpp.location

val dummy_floc: Stdpp.location

val raise_localized_exception: offset:int -> Stdpp.location -> exn -> 'a

(* size in KB (SLOW) *)
val estimate_size: 'a -> int

(* is_prefix_of [prefix] [string], in terms of dirs:
 * foo/bar/ is prefix of foo/bar/baz 
 * foo/bar  is prefix of foo/bar/baz 
 * foo/b    isn't of     foo/bar/baz
 * foo/bar  is prefix of foo/bar 
 *)
val is_prefix_of: string -> string -> bool
val chop_prefix: string -> string -> string
val touch: string -> unit

val profiling_enabled: bool ref
