(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

(** The packages of findlib, for [Setup.init ~packages]: the Elpi package
    [foo] is the findlib package [elpi-foo]. [accumulate "+foo"] dynlinks
    its OCaml code (which registers its plugin), [accumulate "+foo/path"]
    reads a file in its directory, [accumulate "+/path"] a file in the root
    of the project of the accumulating file (the directory of the nearest
    [elpi.toml] above it, see [config_above]). A project declared with
    [declare_project] is found in its root, not in findlib. *)
val packages : Elpi.API.Setup.packages

(** The same, without loading: [accumulate "+foo"] reads the stub of the
    plugin, [foo.builtins.elpi] in the directory of [foo] (e.g. for elpi-lsp,
    that only checks programs) *)
val directories : Elpi.API.Setup.packages

(** Loads the plugin of a package before [Setup.init] (needed if it declares
    state components or quotations); raises [Failure] *)
val preload : string -> unit

(** The configuration of a project, the file [elpi.toml] at its root: keys
    whose value is a string or a list of strings, and [#] comments:
{v
name = "foo"                      # the package of the project
paths = ["lib"]                   # searched by accumulate, like -I
prelude = ["+json/utils"]         # accumulated before the main file
preload = ["pkg"]                 # plugins loaded before Setup.init
v} *)
type config = {
  file : string; (** absolute *)
  name : string option;
  paths : string list; (** absolute, relative ones are relative to [file] *)
  prelude : string list;
  preload : string list;
}

(** raises [Failure] with the file and line of the error; an edited file is
    read again *)
val config_of_file : string -> config

(** the nearest [elpi.toml] in the directory of a file or above it, if any:
    up to the root of a repository (a directory with .git, .hg, _darcs or
    .jj), and not in the home directory or above it *)
val config_above : string -> config option

(** the package named by the [name] of a configuration is found in its root
    (the directory of its [elpi.toml]), not in findlib, e.g. for a project
    being developed: [accumulate "+name/path"] reads its sources; the last
    one declared wins *)
val declare_project : config -> unit

(** [with_prelude config file] is the text of a program that accumulates the
    prelude, then [file] (a path, already resolved, ending in .elpi or .mod;
    raises [Failure] otherwise); it is to be parsed with a location in the
    directory of [config.file] *)
val with_prelude : config -> string -> string
