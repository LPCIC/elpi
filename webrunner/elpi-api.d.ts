// The API of Elpi for JavaScript (web_api.ml), loaded by elpi-api.js
// (api-entry.js): the types of load and of the API it gives, the same for the
// build compiled to WebAssembly and the one compiled to JavaScript.
//
// The functions have the names of the API (src/API.mli) in camelCase. The
// labelled arguments of the API are positional arguments, and the optional
// ones are the fields of a last object, which can be omitted.

// The abstract types of the API: opaque values, to be given back to the
// functions of the API (a value of the wrong type is not checked at run time)
declare const opaque: unique symbol;
type Opaque<Name extends string> = { readonly [opaque]: Name };
export type Elpi = Opaque<"Setup.elpi">;
export type Ast = Opaque<"Ast.program">;
export type Goal = Opaque<"Ast.query">;
export type Program = Opaque<"Compile.program">;
export type Query = Opaque<"Compile.query">;
export type Executable = Opaque<"Compile.executable">;
export type ScopedProgram = Opaque<"Compile.scoped_program">;
export type CompilationUnit = Opaque<"Compile.compilation_unit">;

// Compile.flags: in an argument, a missing field has its default value
// (Compile.defaultFlags); the other flags of the compiler have their default
// value
export interface Flags {
  // the variables of :if
  definedVariables: string[];
  // 0: the first error is thrown; n: the parser and the compiler go on, and
  // return up to n errors
  maxErrors: number;
}

export interface Loc {
  source: string;
  line: number;
  column: number;
  // offsets in the source
  start: number;
  stop: number;
}

// Error.t; text is what Elpi prints (the location, then the message)
export interface ElpiError {
  // who found the error, e.g. "Parser", "Typechecker"
  component: string;
  loc: Loc | null;
  message: string;
  text: string;
}

// Error.warning
export interface Warning extends ElpiError {
  id: "LinearVariable" | "UndeclaredGlobal" | "FlexClause"
    | "ImplicationPrecedence" | "NestedAccumulate";
}

// What the parser and the compiler return: the value (in the field program,
// scopedPrograms or unit), its errors and its warnings
export type WithErrors<K extends string, T> =
  { [k in K]: T } & { errors: ElpiError[]; warnings: Warning[] };

// (unit, cwd) => the absolute path of the file that accumulate reads; it
// throws if there is none, its message is then the error of the accumulate
// directive
export type FileResolver = (unit: string, cwd: string | null) => string;

// Execute.outcome; the terms are pretty-printed, as the REPL prints them
export type Outcome =
  | { outcome: "success"; assignments: { [variable: string]: string };
      constraints: string; state: string }
  | { outcome: "failure" }
  | { outcome: "noMoreSteps" };

// The errors of the API (Error.ElpiError, e.g. a compiler error with
// maxErrors 0, and Parse.ParseError, a syntax error of a program with
// maxErrors 0, without text) are thrown as Errors with the fields of an
// ElpiError; a Failure as an Error
export type ThrownError = Error & Partial<ElpiError>;

export interface Setup {
  // an instance of Elpi, with the standard builtins
  // (Elpi.Builtin.std_builtins); accumulate fails without a fileResolver
  init(options?: { flags?: Partial<Flags>; fileResolver?: FileResolver }): Elpi;
  // f gets what Elpi prints
  setStdFormatter(f: (s: string) => void): void;
  setErrFormatter(f: (s: string) => void): void;
}

export interface Parse {
  // source is the name of the text, for the locations and accumulate
  // (default "(text)")
  programFrom(elpi: Elpi, text: string,
    options?: { source?: string; flags?: Partial<Flags> }): WithErrors<"program", Ast>;
  // a query, or its syntax error, and its warnings; source defaults to
  // "(query)"
  query(elpi: Elpi, text: string, options?: { source?: string }):
    { query: Goal; warnings: Warning[] } | { error: ElpiError; warnings: Warning[] };
}

export interface Compile {
  defaultFlags: Flags;
  program(elpi: Elpi, ast: Ast, options?: { flags?: Partial<Flags> }):
    WithErrors<"program", Program>;

  // separate compilation: a unit is compiled against a base program, which
  // must have what the unit uses, then the base is extended with it. The
  // scoped programs are the one of the text and the ones of the files it
  // accumulates, to be compiled and added in order
  scopeAst(elpi: Elpi, ast: Ast, options?: { flags?: Partial<Flags> }):
    WithErrors<"scopedPrograms", ScopedProgram[]>;
  // it has the builtins already
  emptyBase(elpi: Elpi): Program;
  unit(elpi: Elpi, base: Program, scopedProgram: ScopedProgram,
    options?: { flags?: Partial<Flags> }): WithErrors<"unit", CompilationUnit>;
  extend(base: Program, unit: CompilationUnit, options?: { flags?: Partial<Flags> }):
    WithErrors<"program", Program>;

  // the query, or its first error, and its warnings
  query(program: Program, goal: Goal):
    { query: Query; warnings: Warning[] } | { error: ElpiError; warnings: Warning[] };
  optimize(query: Query): Executable;
}

export interface Execute {
  // the first outcome, within maxSteps steps if given; with
  // delayOutsideFragment, a unification outside the pattern fragment is
  // delayed instead of being an error
  once(executable: Executable,
    options?: { maxSteps?: number; delayOutsideFragment?: boolean }): Outcome;
}

export interface Api {
  Setup: Setup;
  Parse: Parse;
  Compile: Compile;
  Execute: Execute;
}

// The API given by load, and the build that runs it
export interface LoadedApi extends Api {
  backend: "wasm" | "js";
}

export interface LoadOptions {
  // "auto" (the default): the WebAssembly build when the engine supports what
  // it needs, the JavaScript one otherwise or when the WebAssembly one fails
  // to start; "wasm" or "js": that build, or an error
  backend?: "auto" | "wasm" | "js";
}

// Starts a build, once: the next loads give the same API, or fail if it is
// not of the backend they ask for
export declare function load(options?: LoadOptions): Promise<LoadedApi>;

// In a page or a classic web worker, where elpi-api.js is a script
declare global {
  var elpiApi: { load: typeof load } | undefined;
  // the URL of elpi-api.js, when it is not the one of the script or of the
  // worker: web_api.bc.js is next to it
  var elpiApiUrl: string | undefined;
}
