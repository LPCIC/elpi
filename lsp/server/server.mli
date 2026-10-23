(* The language server, independent of how messages come and go: what the
   drivers (../stdio_lsp_driver.ml on stdin/stdout, ../web_driver.ml in a web
   worker) need. A driver calls [init], gives the messages of the client to
   [handle_json], and runs the checks of the opened and changed documents
   ([get_checker_tasks], [check_now]) when it sees fit. *)

open Lsp.Types

(** {2 Initialization} *)

(** [init ~send ~exit ~builtin_library_location ?max_errors ()] must be called
    by the driver before [handle_json]:
    - [send] sends a message to the client;
    - [exit] is called on the exit notification, with the exit code;
    - [builtin_library_location instance name] is where go to definition
      finds a file of the standard library of an instance of Elpi ([name],
      e.g. builtin_stdlib.elpi): the URI that the client is given, and its
      text. A driver that serves the library with the request
      elpi/builtinFile makes the URI with [library_uri];
    - [max_errors] is the maximum number of errors reported for a file
      (default 100); the client can override it with the initialization
      option maxErrors. *)
val init :
  send:(Yojson.Safe.t -> unit) ->
  exit:(int -> unit) ->
  builtin_library_location:(Checker.instance -> string -> (DocumentUri.t * string) option) ->
  ?max_errors:int ->
  unit -> unit

(** [library_uri ~prefix instance name] is [prefix]ID/NAME, the URI of the file
    [name] of the library of [instance] (ID is [Checker.id instance]): the
    request elpi/builtinFile answers its text while a document of that
    instance is open *)
val library_uri : prefix:string -> Checker.instance -> string -> string

(** {2 Messages} *)

(** handles a message of the client (a request is answered with [send]).
    @raise Invalid_argument if [init] was not called *)
val handle_json : Yojson.Safe.t -> unit

(** {2 Checks} *)

(** Checking a document is not done upfront: when a document is opened or
    changed, [handle_json] only records a check to run, a checker task. The
    driver takes the tasks with [get_checker_tasks] and runs them with
    [check_now], with any scheduling it likes: at once, or (as both drivers
    do) when the user has stopped typing, so that a burst of keystrokes costs
    one check. A request that needs a checked document (hover, definition...)
    checks it on demand, whatever the scheduling. *)

(** a check to run: a version of a document *)
type checker_task

(** the checker tasks of the documents opened or changed since their last
    task was taken (none if the list is empty); each task is given once *)
val get_checker_tasks : unit -> checker_task list

(** runs a task, unless its document was closed, changed since, or already
    checked; if another document changed since the task was taken (the user is
    typing), the task is given again by [get_checker_tasks] instead *)
val check_now : checker_task -> unit

