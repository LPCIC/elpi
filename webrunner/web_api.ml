(* The API of Elpi (API.mli) for JavaScript: its modules Setup, Parse, Compile
   and Execute, compiled to JavaScript (web_api.bc.js) or to WebAssembly
   (web_api.bc.wasm.js). It is loaded by elpi-api.js (api-entry.js), which
   picks a build: when it starts, the build gives the API, an object with these
   modules, to the function globalThis.__elpiApiReady that elpi-api.js sets.

   - the functions have the names of the API in camelCase, and take the
     labelled arguments of the API as positional arguments, the optional ones
     last, in an object (e.g. { flags });
   - the abstract types of the API (Ast.program, Compile.program, ...) are
     opaque values, to be given back to the functions of the API;
   - errors and warnings are objects { component, loc, message, text } (and
     id, for a warning), where loc is null or
     { source, line, column, start, stop } and text is what Elpi prints;
   - ElpiError and ParseError (of a program with maxErrors 0) are thrown as
     Error objects with the same fields;
   - the terms of a solution are pretty-printed, as the REPL does.

   Accumulated files are read with the file system of Node, or with the
   pseudo file system of js_of_ocaml in a browser. The builtins are the
   standard ones (Elpi.Builtin.std_builtins). *)

open Js_of_ocaml
open Elpi
open API

type any = Js.Unsafe.any

let inject = Js.Unsafe.inject
let str s : any = inject (Js.string s)
let int n : any = inject (Js.number_of_float (float_of_int n))
let obj fields : any = inject (Js.Unsafe.obj (Array.of_list fields))
let array f l : any = inject (Js.array (Array.of_list (List.map f l)))
let null : any = inject Js.null

(* an optional argument, or a field of an object: None if undefined or null *)
let opt (v : any) : any option =
  if Js.Unsafe.equals v Js.undefined || Js.Unsafe.equals v Js.null then None else Some v
let field (o : any) name : any option =
  match opt o with None -> None | Some o -> opt (Js.Unsafe.get o name)
let to_string (v : any) = Js.to_string (Js.Unsafe.coerce v)
let to_bool (v : any) = Js.to_bool (Js.Unsafe.coerce v)
let to_int (v : any) = int_of_float (Js.float_of_number (Js.Unsafe.coerce v))
let to_list f (v : any) = List.map f (Array.to_list (Js.to_array (Js.Unsafe.coerce v)))

(* opaque values of the API, given to JavaScript and back *)
let opaque (x : 'a) : any = Obj.magic x
let of_opaque (v : any) : 'a = Obj.magic v

(* locations, errors and warnings *)

let loc { Ast.Loc.source_name; source_start; source_stop; line; line_starts_at; _ } = obj [
  "source", str source_name;
  "line", int line;
  "column", int (source_start - line_starts_at);
  "start", int source_start;
  "stop", int source_stop;
]
let loc_opt = function None -> null | Some l -> loc l

let error_fields ({ Error.component; loc = l; message } as e) = [
  "component", str component;
  "loc", loc_opt l;
  "message", str message;
  "text", str (Error.show e);
]
let error e = obj (error_fields e)

let warning_id = function
  | Error.LinearVariable -> "LinearVariable"
  | Error.UndeclaredGlobal -> "UndeclaredGlobal"
  | Error.FlexClause -> "FlexClause"
  | Error.ImplicationPrecedence -> "ImplicationPrecedence"
  | Error.NestedAccumulate -> "NestedAccumulate"
let warning { Error.warning_id = id; warning } = obj (("id", str (warning_id id)) :: error_fields warning)

(* a query parsed or compiled: { query, warnings } or { error, warnings } *)
let query_result (result, warnings) =
  let warnings = "warnings", array warning warnings in
  match result with
  | Ok q -> obj [ "query", opaque q; warnings ]
  | Error e -> obj [ "error", error e; warnings ]

(* the result of the parser and of the compiler: the value, its errors and its
   warnings *)
let with_errors name f (x, errors, warnings) =
  obj [ name, f x; "errors", array error errors; "warnings", array warning warnings ]

(* [e] thrown by JavaScript code: with WebAssembly, an error thrown by the OCaml
   code (Js.Js_error.raise_) can reach the caller as a WebAssembly.Exception
   that wraps it (e.g. with Node 22), not as the error itself *)
let js_throw : any -> 'a =
  let f = Js.Unsafe.pure_js_expr "(function (e) { throw e; })" in
  fun e -> Js.Unsafe.fun_call f [| e |]

(* an Error with the fields of [fields] *)
let throw message fields =
  let e = Js.Unsafe.new_obj (Js.Unsafe.get Js.Unsafe.global "Error") [| str message |] in
  List.iter (fun (k, v) -> Js.Unsafe.set e k v) fields;
  js_throw e

(* the exceptions of the API become Errors *)
let guard f =
  try f () with
  | Error.ElpiError e -> throw (Error.show e) (error_fields e)
  | Parse.ParseError (l, message) ->
      throw (Format.asprintf "%a@\n%s" Ast.Loc.pp l message)
        [ "component", str "Parser"; "loc", loc l; "message", str message ]
  | Failure message -> throw message [ "message", str message ]
  | Js.Js_error.Exn e -> js_throw (inject (Js.Js_error.to_error e))
  (* any other exception, e.g. Division_by_zero raised by a builtin *)
  | e -> let message = Printexc.to_string e in throw message [ "message", str message ]

let fn1 f = inject (Js.Unsafe.callback_with_arity 1 (fun a -> guard (fun () -> f a)))
let fn2 f = inject (Js.Unsafe.callback_with_arity 2 (fun a b -> guard (fun () -> f a b)))
let fn3 f = inject (Js.Unsafe.callback_with_arity 3 (fun a b c -> guard (fun () -> f a b c)))
let fn4 f = inject (Js.Unsafe.callback_with_arity 4 (fun a b c d -> guard (fun () -> f a b c d)))

(* flags: { definedVariables, maxErrors }, the missing ones are the default
   ones; the other flags of the compiler are the default ones *)

let flags_of (o : any) =
  let d = Compile.default_flags in
  { d with
    Compile.defined_variables =
      Option.fold ~none:d.defined_variables
        ~some:(fun v -> Compile.StrSet.of_list (to_list to_string v)) (field o "definedVariables");
    max_errors = Option.fold ~none:d.max_errors ~some:to_int (field o "maxErrors");
  }
let flags_opt (options : any) = Option.map flags_of (field options "flags")

let flags { Compile.defined_variables; max_errors; _ } = obj [
  "definedVariables", array str (Compile.StrSet.elements defined_variables);
  "maxErrors", int max_errors;
]

(* a formatter that gives what it prints to the JavaScript function [f] *)
let formatter_of (f : any) =
  Format.make_formatter
    (fun s pos len -> ignore (Js.Unsafe.fun_call f [| str (String.sub s pos len) |]))
    (fun () -> ())

(* file resolvers: (unit, cwd) => absolute path, throwing if not found *)

let resolver_of (f : any) ?cwd ~unit () =
  try to_string (Js.Unsafe.fun_call f [| str unit; Option.fold ~none:null ~some:str cwd |])
  with Js.Js_error.Exn e -> failwith (Js.Js_error.message e)

(* Setup *)

let setup = obj [
  (* init({ flags, fileResolver }) *)
  "init", fn1 (fun options ->
    opaque (Setup.init
      ?flags:(Option.map Compile.to_setup_flags (flags_opt options))
      ?file_resolver:(Option.map resolver_of (field options "fileResolver"))
      ~builtins:[Builtin.std_builtins] ()));
  (* setStdFormatter(f), setErrFormatter(f): f(string) gets what Elpi prints *)
  "setStdFormatter", fn1 (fun f -> Setup.set_std_formatter (formatter_of f); null);
  "setErrFormatter", fn1 (fun f -> Setup.set_err_formatter (formatter_of f); null);
]

(* Parse *)

let source options default = Option.fold ~none:default ~some:to_string (field options "source")

let parse = obj [
  (* programFrom(elpi, text, { source, flags }): source is the name of the
     text, for the locations and accumulate *)
  "programFrom", fn3 (fun elpi text options ->
    let text = to_string text in
    with_errors "program" opaque
      (Parse.program_from ?flags:(flags_opt options) ~elpi:(of_opaque elpi)
         ~loc:(Ast.Loc.initial (source options "(text)")) ~digest:(Digest.string text)
         (Lexing.from_string text)));
  (* query(elpi, text, { source }): { query, warnings } or { error, warnings } *)
  "query", fn3 (fun elpi text options ->
    query_result (Parse.query ~elpi:(of_opaque elpi) ~loc:(Ast.Loc.initial (source options "(query)"))
      ~text:(to_string text)));
]

(* Compile *)

let compile = obj [
  "defaultFlags", flags Compile.default_flags;
  (* program(elpi, ast, { flags }) *)
  "program", fn3 (fun elpi ast options ->
    with_errors "program" opaque (Compile.program ?flags:(flags_opt options) ~elpi:(of_opaque elpi) (of_opaque ast)));

  (* scopeAst(elpi, ast, { flags }): { scopedPrograms, errors, warnings } *)
  "scopeAst", fn3 (fun elpi ast options ->
    with_errors "scopedPrograms" (array opaque)
      (Compile.scope_ast ?flags:(flags_opt options) ~elpi:(of_opaque elpi) (of_opaque ast)));
  "emptyBase", fn1 (fun elpi -> opaque (Compile.empty_base ~elpi:(of_opaque elpi)));
  (* unit(elpi, base, scopedProgram, { flags }): { unit, errors, warnings } *)
  "unit", fn4 (fun elpi base sp options ->
    with_errors "unit" opaque
      (Compile.unit ?flags:(flags_opt options) ~elpi:(of_opaque elpi) ~base:(of_opaque base) (of_opaque sp)));
  (* extend(base, unit, { flags }) *)
  "extend", fn3 (fun base u options ->
    with_errors "program" opaque (Compile.extend ?flags:(flags_opt options) ~base:(of_opaque base) (of_opaque u)));

  (* query(program, goal): { query, warnings } or { error, warnings } *)
  "query", fn2 (fun p g -> query_result (Compile.query (of_opaque p) (of_opaque g)));
  "optimize", fn1 (fun q -> opaque (Compile.optimize (of_opaque q)));
]

(* Execute *)

let outcome = function
  | Execute.Success { Data.assignments; constraints; state; pp_ctx; _ } -> obj [
      "outcome", str "success";
      "assignments", obj (List.map (fun (name, t) -> name, str (Format.asprintf "%a" (Pp.term pp_ctx) t))
        (Data.StrMap.bindings assignments));
      "constraints", str (Format.asprintf "%a" (Pp.constraints pp_ctx) constraints);
      "state", str (Format.asprintf "%a" Pp.state state);
    ]
  | Failure -> obj [ "outcome", str "failure" ]
  | NoMoreSteps -> obj [ "outcome", str "noMoreSteps" ]

let delay options = Option.map to_bool (field options "delayOutsideFragment")

let execute = obj [
  (* once(executable, { maxSteps, delayOutsideFragment }): { outcome:
     "success", assignments, constraints, state } or { outcome: "failure" }
     or { outcome: "noMoreSteps" } *)
  "once", fn2 (fun exe options ->
    outcome (Execute.once ?max_steps:(Option.map to_int (field options "maxSteps"))
      ?delay_outside_fragment:(delay options) (of_opaque exe)));
]

(* the API, to elpi-api.js; without it (the build loaded by itself) nothing *)
let () =
  let ready = Js.Unsafe.get Js.Unsafe.global "__elpiApiReady" in
  if Option.is_some (opt ready) then
    ignore (Js.Unsafe.fun_call ready
      [| obj [ "Setup", setup; "Parse", parse; "Compile", compile; "Execute", execute ] |])
