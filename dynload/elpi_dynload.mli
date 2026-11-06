(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

(** The packages of findlib, for [Setup.init ~packages]: [accumulate
    "+pkg"] dynlinks the OCaml code of package [pkg] (which registers its
    plugin), [accumulate "+pkg/path"] reads a file in its directory *)
val packages : Elpi.API.Setup.packages

(** The same, without loading: [accumulate "+pkg"] reads the stub of the
    plugin, [pkg.plugin.elpi] in the directory of [pkg] (e.g. for elpi-lsp,
    that only checks programs) *)
val directories : Elpi.API.Setup.packages

(** Loads the plugin of a package before [Setup.init] (needed if it declares
    state components or quotations); raises [Failure] *)
val preload : string -> unit

(** The configuration of a project, the file [elpi.toml]: keys whose value is
    a list of strings, and [#] comments:
{v
paths = ["lib"]                   # searched by accumulate, like -I
prelude = ["+elpi-json/utils"]    # accumulated before the main file
preload = ["pkg"]                 # plugins loaded before Setup.init
v} *)
type config = {
  file : string;
  paths : string list; (** absolute, relative ones are relative to [file] *)
  prelude : string list;
  preload : string list;
}

(** raises [Failure] with the file and line of the error *)
val config_of_file : string -> config

(** the [elpi.toml] next to a file, if any *)
val config_next_to : string -> config option

(** [with_prelude config file] is the text of a program that accumulates the
    prelude, then [file]; it is to be parsed with a location in the directory
    of [config.file] *)
val with_prelude : config -> string -> string
