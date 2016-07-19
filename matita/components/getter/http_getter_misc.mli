(*
 * Copyright (C) 2003-2004:
 *    Stefano Zacchiroli <zack@cs.unibo.it>
 *    for the HELM Team http://helm.cs.unibo.it/
 *
 *  This file is part of HELM, an Hypertextual, Electronic
 *  Library of Mathematics, developed at the Computer Science
 *  Department, University of Bologna, Italy.
 *
 *  HELM is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU General Public License
 *  as published by the Free Software Foundation; either version 2
 *  of the License, or (at your option) any later version.
 *
 *  HELM is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with HELM; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 *  MA  02111-1307, USA.
 *
 *  For details, see the HELM World-Wide-Web page,
 *  http://helm.cs.unibo.it/
 *)

 (** 'mkdir' failed, arguments are: name of the directory to be created and
 failure reason *)
exception Mkdir_failure of string * string

  (** @return Some localpart for URI belonging to the "file://" scheme, None for
  * other URIs
  * removes trailing ".gz", if any
  * e.g.: local_url "file:///etc/passwd.gz" = Some "/etc/passwd"
  *       local_url "http://...." = None *)
val local_url: string -> string option

 (** "fold_left" like function on file lines, trailing newline is not passed to
 the given function *)
val fold_file : (string -> 'a -> 'a) -> 'a -> string -> 'a

 (* "iter" like function on file lines, trailing newline is not passed to the
 given function *)
val iter_file : (string -> unit) -> string -> unit

 (* "iter" like function on file data chunks of fixed size *)
val iter_file_data: (string -> unit) -> string -> unit

  (** like Hashtbl.fold but keys are processed ordered *)
val hashtbl_sorted_fold :
  ('a -> 'b -> 'c -> 'c) -> ('a, 'b) Hashtbl.t -> 'c -> 'c
  (** like Hashtbl.iter but keys are processed ordered *)
val hashtbl_sorted_iter : ('a -> 'b -> unit) -> ('a, 'b) Hashtbl.t -> unit

val list_uniq: 'a list -> 'a list (* uniq unix filter on lists *)

  (** cp frontend *)
val cp: string -> string -> unit
  (** wget frontend, if output is given it is the destination file, otherwise
  standard wget rules are used. Additionally this function support also the
  "file://" scheme for file system addressing *)
val wget: ?output: string -> string -> unit
  (** gzip frontend. If keep = true original file will be kept, default is
  false. output is the file on which gzipped data will be saved, default is
  given file with an added ".gz" suffix *)
val gzip: ?keep: bool -> ?output: string -> string -> unit
  (** gunzip frontend. If keep = true original file will be kept, default is
  false. output is the file on which gunzipped data will be saved, default is
  given file name without trailing ".gz" *)
val gunzip: ?keep: bool -> ?output: string -> string -> unit
  (** tempfile frontend, return the name of created file. A special purpose
  suffix is used (actually "_http_getter" *)
val tempfile: unit -> string
  (** mkdir frontend, if parents = true also parent directories will be created.
  If the given directory already exists doesn't act.
  parents defaults to false *)
val mkdir: ?parents:bool -> string -> unit

  (** pretty printer for Unix.process_status values *)
val string_of_proc_status : Unix.process_status -> string

  (** raw URL downloader, return Some the contents of downloaded resource or
  None if an error occured while downloading. This function support also
  "file://" scheme for filesystem resources *)
val http_get: string -> string option

  (** true on blanks-only and #-commented lines, false otherwise *)
val is_blank_line: string -> bool

val normalize_dir: string -> string (** add trailing "/" if missing *)
val strip_trailing_slash: string -> string
val strip_suffix: suffix:string -> string -> string

val extension: string -> string  (** @return string part after rightmost "." *)

val temp_file_of_uri: string -> string * out_channel

  (** execute a command and return first line of what it prints on stdout *)
val backtick: string -> string

