(** Common code of the tests of elpi-lsp.

    A test is a script, one per [.elpi] file of the test directory, written in
    a [script_NAME.ml] module that registers itself with {!register}. The
    driver ({!main}, called by [test_lsp.ml]) starts the server given on the
    command line ([test_lsp SERVER DIR], where [DIR] holds the [.elpi] files),
    runs the scripts one after the other, and prints what the server answers.
    The output of the script [NAME] goes to [NAME.output], to be compared with
    [NAME.expected]; the rest (the capabilities of the server, its shutdown)
    goes to the standard output.

    All the functions below print a summary of the answers of the server, to
    be compared with the expected output. Files are named relative to the test
    directory. *)

(** {2 Scripts} *)

(** [register ~name file script] registers a script. [script file] is run by
    {!main}, after all the scripts have been registered, in the order of
    [name]; it opens [file] and queries the server. [name] must be unique
    (otherwise [Failure] is raised) and names the file with the expected
    output; by convention it is the name of [file] without [.elpi], followed by
    something if there are several scripts for the same file. After the
    script, [file] is closed, so that the next script starts from a clean
    document. *)
val register : name:string -> string -> (string -> unit) -> unit

(** Runs the registered scripts: starts with [initialize] and prints the
    capabilities of the server, ends with [shutdown] and [exit], and prints
    the exit code of the server. *)
val main : unit -> unit

(** {2 Helpers for the scripts} *)

(** [section fmt …] prints a marker [==== title ====] that separates the steps
    of a script (and a blank line before it, but for the first one). *)
val section : ('a, unit, string, unit) format4 -> 'a

(** The contents of a file of the test directory. *)
val read_file : string -> string

(** {2 Requests} *)

(** [open_file file] sends [didOpen] with the contents of [file] and prints the
    diagnostics that the server publishes: for each one its range, severity
    and message, and the text of the range underlined in its line (nothing
    for an empty range). *)
val open_file : string -> unit

(** [change_file_burst file version texts] sends several [didChange] in a row
    ([version] is the version of the first one) and prints the diagnostics of the
    first answer of the server. Changes are checked after a pause, so there is
    one answer, for the last text. *)
val change_file_burst : string -> int -> string list -> unit

(** [close_file file] sends [didClose]; the server then publishes no
    diagnostics for [file]. *)
val close_file : string -> unit

(** [change_file file version text] sends [didChange] with the whole [text]
    as the new contents of the open [file], and prints the diagnostics as
    {!open_file} does. *)
val change_file : string -> int -> string -> unit

(** [hover file needle k] requests the hover at the [k]-th character after the
    first occurrence of [needle] in [file]. It prints the cursor position and the
    hovered range, the lines involved with the range ([^]) and the cursor ([*])
    marked under them, and the text of the popup (prefixed by [?]); or [none]
    if the server has no answer. *)
val hover : string -> string -> int -> unit

(** [definition_file file needle k] is the path of the file where the symbol at
    the position is defined, as the server says (a file of the standard library,
    that the server generates). *)
val definition_file : string -> string -> int -> string option

(** Whether the file cannot be written. *)
val is_read_only : string -> bool

(** [semantic_tokens file] requests the colors of [file] and prints the lines
    where there are tokens, with a row of marks under each for every type of
    token ([^]), and one for the tokens that are a declaration ([=], the
    binders of the variables). *)
val semantic_tokens : string -> unit

(** [highlight file needle k] requests the highlights of the variable or
    constant at the [k]-th character after the first occurrence of [needle] in
    [file] (the server calls them write and read). It prints the range of the
    definition site and of each occurrence, and then each line of the file where
    there is one, with rows of marks under it: [*] the cursor, [=] the definition
    site, [^] the occurrences. The definition site of a variable is its binder
    (the [pi x\\] or [sigma x\\] or [x\\] that binds a bound variable, the head of
    the rule for a unification variable); the one of a constant is its
    declaration, when it is in [file]. It prints [none] if the server has no
    answer, that is when the cursor is not on a variable or a constant. *)
val highlight : string -> string -> int -> unit

(** [definition file needle k] requests the definition of the symbol at the
    [k]-th character after the first occurrence of [needle] in [file]. It
    prints the cursor position and its line with the cursor ([*]) marked, the
    location (file and range) and the source text of the range; or [none] if
    the server has no answer: the server cannot tell why (a symbol of the
    standard library is defined in a file that is not on the disk, a keyword or
    a literal has no definition), so the script can say it with [~none], which
    is printed after [none]. *)
val definition : ?none:string -> string -> string -> int -> unit

(** [run ?file ?text ?max_steps query] sends the request [elpi/run] for
    [query] on the document [file] (an open file of the test directory), or on
    [text] (then [file] is where the text is, e.g. [""] for the test
    directory), with the parameter [maxSteps] if given (as JSON, to test wrong
    values too), and prints the result: the status, then what the program
    printed ([|]), the errors ([!]) and the diagnostics ([#]); or the error of
    the request. *)
val run : ?file:string -> ?text:string -> ?max_steps:Yojson.Safe.t -> string -> unit
