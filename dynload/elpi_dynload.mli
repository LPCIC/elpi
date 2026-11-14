(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

(** The packages of findlib, for [Setup.init ~packages]: the package [pkg]
    of ["+pkg"] is the findlib package [pkg], named as findlib does (e.g.
    [elpi-json], [rocq-elpi]). [accumulate "+pkg"] dynlinks its OCaml code
    (which registers its plugin under the name [pkg]), [accumulate
    "+pkg/path"] reads a file in its directory, [accumulate "+/path"] a file
    in the root of the project of the accumulating file (the directory of the
    nearest [elpi.toml] above it, see [config_above]). A project declared
    with [declare_project] is found in its root, not in findlib. *)
val packages : Elpi.API.Setup.packages

(** The same, without loading: [accumulate "+pkg"] reads the stub of the
    plugin, [pkg.builtins.elpi] in the directory of [pkg] (e.g. for elpi-lsp,
    that only checks programs) *)
val packages_stubs : Elpi.API.Setup.packages

(** Loads the plugin of a package before [Setup.init] (needed if it declares
    state components or quotations); raises an [Elpi.API.Error.ElpiError] *)
val preload : pkg:string -> unit

(** The configuration of a project, the file [elpi.toml] at its root: keys
    whose value is a string or a list of strings, the sections [paths] and
    [warnings], and [#] comments:
{v
name = "foo"                      # the findlib package of the project (required)
use = ["+bar"]                    # the elpi.toml of bar is used too
prelude = ["+elpi-json/utils"]    # builtins of Setup.init, before the files
preload = ["pkg"]                 # plugins loaded before Setup.init
[paths]                           # where accumulate finds files
"" = "+/lib"                      # any file, like -I
"a.b" = ["+/src/b", "+/gen/b"]    # a.b/x is src/b/x, or else gen/b/x
"c" = "+pkg/dir"                  # c/x is dir/x in the directory of package pkg
[dev-only-paths]                  # the same, for the project's own development:
"t" = "+/tests"                   # not used by a project that uses it
[warnings]                        # the levels of the kinds of warnings
linear-variable = "off"           # "off", "on" or "error"; all is all of them
undeclared-global = "error"
v}
    A file or a directory is ["+/x"] (relative to [elpi.toml]), ["+pkg/x"]
    or absolute: a relative one is an error, so that an [elpi.toml]
    installed with its package (next to its META) means the same. The
    [paths], [prelude] and [preload] of the packages of [use], whose
    [elpi.toml] is in their directory, are added to the ones of the project,
    transitively: [paths] after its own ones, [prelude] and [preload]
    before; their [dev-only-paths] are not. The [name] of the [elpi.toml]
    of a package of [use] must be the findlib name of the package. *)
type config = {
  file : string; (** absolute *)
  name : string; (** the findlib name of its package *)
  use : string list; (** as written *)
  paths : (string * string) list;
      (** the prefix ([""] for any file) and an absolute directory, in order
          (the ones of [use] last): see [Parse.std_resolver] *)
  dev_only_paths : (string * string) list;
      (** as [paths], only the ones of this file (never the ones of [use]):
          a host adds them after [paths] when the project is its own *)
  prelude : string list;
      (** ["+pkg"], ["+pkg/file"] or an absolute file, the ones of [use]
          first *)
  preload : string list; (** the ones of [use] first *)
  warnings : (Elpi.API.Error.warning_id * Elpi.API.Error.warning_level) list;
      (** in the order of the file, see [Elpi.API.Error.warning_level]; not
          the ones of [use] *)
}

(** raises an [Elpi.API.Error.ElpiError] located at the line of the error;
    an edited file is read again, also when an [elpi.toml] of [use] changed *)
val config_of_file : file:string -> config

(** the nearest [elpi.toml] in the directory of a file or above it, if any:
    up to the root of a repository (a directory with .git, .hg, dune-workspace,
    _RocqProject or _CoqProject), and not in the home directory or above it *)
val config_above : file:string -> config option

(** the package named by the [name] of a configuration is found in its root
    (the directory of its [elpi.toml]), not in findlib, e.g. for a project
    being developed: [accumulate "+name/path"] reads its sources; the last
    one declared wins *)
val declare_project : config -> unit

(** [prelude_builtins config] are the builtins of the prelude of [config],
    for [Setup.init] (after the builtins of the host): so their macros are
    visible in every file of the project. An entry is found as [accumulate]
    finds it: ["+pkg"] is the plugin of [pkg] if it is registered, its stub
    [pkg.builtins.elpi] otherwise. A file is the text of the builtins, and can accumulate
    other files. Raises an [Elpi.API.Error.ElpiError] *)
val prelude_builtins : config -> Elpi.API.Setup.builtins list

(** The result of an item of [check_package]: what was found, or the errors *)
type check_result = Checked of string | Failed of string list

(** The items checked, in order: ["elpi.toml"], ["+pkg"], then each
    ["+pkg/file"] *)
type report = (string * check_result) list

(** [check_package ~pkg] checks the package [pkg] as findlib installed it (a
    project declared with [declare_project] is not used):
    - its [elpi.toml] (if any), read as [use] reads it: its [name] is [pkg],
      its [dev-only-paths] are not used;
    - if it has a stub [pkg.builtins.elpi], its plugin: it is dynlinked and
      registers under [pkg], its stub compiles and is its documentation
      ([BuiltIn.document_fmt]);
    - each [.elpi] file in its directory (the stubs aside), as
      [accumulate "+pkg/file"] reads it: it is parsed and compiled, as
      elpi-lsp does with a document of a project that uses [pkg] (its
      preload, prelude and paths, the stubs of the plugins), so its
      accumulated files are found where the package is installed. *)
val check_package : pkg:string -> report
