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

(** Configuration repository for HELM applications.
 *
 * ++ Keys format ++
 *
 *  key ::= path
 *  path ::= component ( '.' component )*
 *  component ::= ( alpha | num | '_' )+
 *  # with the only exception that sequences of '_' longer than 1 aren't valid
 *  # components
 *
 *  Suggested usage <application>.<setting>:
 *   e.g. gTopLevel.prooffile, http_getter.port, ...
 *
 * ++ Configuration file example ++
 *
 *  gTopLevel.prooffile = "/home/zack/prooffile"
 *  http_getter.port = "58080"
 *
 * ++ Environment variable override ++
 *
 *  each key has an associated environment variable name. At runtime (i.e. when
 *  "get" requests are performed) a variable with this name will be looked for,
 *  if it's defined it will override the value present (or absent) in the
 *  registry.
 *  Environment variables are _not_ considered when saving the configuration to
 *  a configuration file (via "save_to" function below) .
 *
 *  Mapping between keys and environment variables is as follows:
 *  - each "." is converted to "__"
 *  E.g.: my.Foo_iSH.Application -> my__Foo_iSH__Application
 *
 * ++ Variable interpolation ++
 *
 * Interpolation is supported with the following syntax:
 *  
 *  foo.bar = "quux"
 *  foo.baz = $(foo.bar)/baz
 *)

  (** raised when a looked up key can't be found
   * @param key looked up key *)
exception Key_not_found of string

  (** raised when a cyclic definitions is found, e.g. after
   * Helm_registry.set "a" "$b"
   * Helm_registry.set "b" "$a"
   * @param msg brief description of the definition cycle *)
exception Cyclic_definition of string

  (** raised when a looked up key doesn't have the required type, parameter is
   * an error message *)
exception Type_error of string

  (** raised when a malformed key is encountered
   * @param key malformed key *)
exception Malformed_key of string

  (** raised when an error is encountered while parsing a configuration file
   * @param fname file name 
   * @param line line number
   * @param col column number
   * @param msg error description
   *)
exception Parse_error of string * int * int * string

(** {2 Generic untyped interface}
 * Using the functions below this module could be used as a repository of
 * key/value pairs *)

  (** lookup key in registry with environment variable override *)
val get: string -> string
val set: key:string -> value:string -> unit
val has: string -> bool

  (** remove a key from the current environment, next get over this key will
   * raise Key_not_found until the key will be redefined *)
val unset: string -> unit

  (** @param interpolate defaults to true *)
val fold:
  ?prefix:string -> ?interpolate:bool ->
    ('a -> string -> string -> 'a) -> 'a -> 'a

  (** @param interpolate defaults to true *)
val iter:
  ?prefix:string -> ?interpolate:bool -> 
    (string -> string -> unit) -> unit

  (** @param interpolate defaults to true *)
val to_list:
  ?prefix:string -> ?interpolate:bool ->
    unit -> (string * string) list

  (** @param prefix key representing the section whose contents should be listed
  * @return section list * key list *)
val ls: string -> string list * string list

(** {2 Typed interface}
 * Three basic types are supported: strings, int and strings list. Strings
 * correspond literally to what is written inside double quotes; int to the
 * parsing of an integer number from ; strings list to the splitting at blanks
 * of it (heading and trailing blanks are removed before splitting) *)

(** {3 Unmarshallers} *)

val string:       string -> string
val int:          string -> int
val float:        string -> float
val bool:         string -> bool
val pair:         (string -> 'a) -> (string -> 'b) -> string -> 'a * 'b
val triple:       (string -> 'a) -> (string -> 'b) -> (string -> 'c) -> string -> 'a * 'b * 'c
val quad:         (string -> 'a) -> (string -> 'b) -> (string -> 'c) -> (string -> 'd) -> string -> 'a * 'b * 'c * 'd

(** {3 Typed getters} *)

  (** like get, with an additional unmarshaller
   * @param unmarshaller conversion function from string to the desired type.
   * Use one of the above unmarshallers *)
val get_typed: (string -> 'a) -> string -> 'a

val get_opt: (string -> 'a) -> string -> 'a option
val get_opt_default: (string -> 'a) -> default:'a -> string -> 'a

  (** never fails with Key_not_found, instead return the empty list *)
val get_list: (string -> 'a) -> string -> 'a list

  (** decode values which are blank separated list of values, of length 2 *)
val get_pair: (string -> 'a) -> (string -> 'b) -> string -> 'a * 'b

  (** decode values which are blank separated list of values, of length 3 *)
val get_triple: (string -> 'a) -> (string -> 'b) -> (string -> 'c) -> string -> 'a * 'b * 'c

  (** decode values which are blank separated list of values, of length 4 *)
val get_quad: (string -> 'a) -> (string -> 'b) -> (string -> 'c) -> (string -> 'd) -> string -> 'a * 'b * 'c * 'd

(** {4 Shorthands} *)

val get_string: string -> string
val get_int:    string -> int
val get_float:  string -> float
val get_bool:   string -> bool

(** {3 Marshallers} *)

val of_string:      string      -> string
val of_int:         int         -> string
val of_float:       float       -> string
val of_bool:        bool        -> string

(** {3 Typed setters} *)

  (** like set, with an additional marshaller
   * @param marshaller conversion function to string.
   * Use one of the above marshallers *)
val set_typed: ('a -> string) -> key:string -> value:'a -> unit

val set_opt: ('a -> string) -> key:string -> value:'a option -> unit
val set_list: ('a -> string) -> key:string -> value:'a list -> unit

(** {4 Shorthands} *)

val set_string: key:string -> value:string  -> unit
val set_int:    key:string -> value:int     -> unit
val set_float:  key:string -> value:float   -> unit
val set_bool:   key:string -> value:bool    -> unit

(** {2 Persistent configuration} *)

  (** @param fname file to which save current configuration *)
val save_to: string -> unit

  (** @param fname file from which load new configuration. If it's an absolute
   * file name "path" argument is ignored.
   * Otherwise given file name is looked up in each directory member of the
   * given path. Each matching file is loaded overriding previous settings. If
   * no path is given a default path composed of just the current working
   * directory is used.
   *)
val load_from: ?path:string list -> string -> unit

  (** removes all keys *)
val clear: unit -> unit 

