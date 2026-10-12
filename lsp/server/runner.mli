(* Running a query on a program, for the request elpi/run *)

(** [run ?max_steps ~instance ~path ~text ~query ()] parses and compiles
    [text] (the file [path], for the locations and accumulate) with
    [instance], then runs [query] (a final
    dot is optional) once, for at most [max_steps] steps of the interpreter
    (then the status is failure, with the error "no more steps"). The result
    is
    {v
    { status: "success" | "failure" | "error", output: string,
      errors: [string], diagnostics: [string],
      assignments?: { [name]: string }, constraints?: [string] }
    v}
    - status: "success" if the query succeeds, "failure" if it fails, "error"
      if the query has syntax or type errors, if running it raises an error,
      or if the program cannot be compiled at all. A program with errors is
      run anyway, without the declarations and rules that have errors;
    - output: what the program printed;
    - diagnostics: the errors and the warnings of the program, each with its
      location: what the server publishes as the diagnostics of the document,
      so a client that shows those (e.g. an editor) needs not show them again;
    - errors: the rest, i.e. the errors and the warnings of the query and of
      its run (e.g. "no more steps"), and last, if the program has errors, a
      warning that it could not be fully compiled, with the number of its
      errors (they are in diagnostics);
    - assignments: only on success, the value of each variable of the query;
    - constraints: only on success, the constraints left by the run, as the REPL
      prints them, e.g. "{c0} : hyps ?- goal /* suspended on X0 */". *)
val run :
  ?max_steps:int -> instance:Checker.instance -> path:string -> text:string -> query:string -> unit ->
  Yojson.Safe.t
