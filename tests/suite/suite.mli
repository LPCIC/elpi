
module Util : sig

  val strip_cwd : string -> string

  val has_substring : sub:string -> string -> bool

end

module Test : sig

type fname = string

type expectation =
  | Success
  | Failure
  | SuccessOutput of Str.regexp
  | FailureOutput of Str.regexp
  | SuccessOutputTxt of (string list -> bool)
  | SuccessOutputFile of { sample : string; adjust : string -> string; reference : string }

type trace = Off | On of string list

val declare :
  (*name*)string ->
  description:string ->
  ?source_elpi:fname ->
  ?source_teyjus:fname ->
  ?deps_teyjus:fname list ->
  ?source_dune:fname ->
  ?source_json:fname ->
  ?after:string ->
  ?typecheck:bool ->
  ?input:fname -> 
  ?expectation:expectation -> 
  ?outside_llam:bool ->
  ?trace:trace ->
  ?legacy_parser:bool ->
  ?promote:bool ->
  category:string ->
  unit -> unit

type t = {
  name : string;
  description : string;
  category: string;
  source_elpi : fname option;
  source_teyjus : fname option;
  deps_teyjus : fname list;
  source_dune : fname option;
  source_json : fname option;
  after : string list;
  typecheck : bool;
  input : fname option;
  expectation : expectation;
  outside_llam : bool;
  trace: string list;
  legacy_parser : bool;
}

val get : catskip:string list -> (name:string -> bool) -> t list

val names : unit -> (string * string list) list (* grouped by category *)

end

module Runner : sig

type time = {
  execution : float;
  typechecking : float;
  walltime : float;
  mem : int;
}
type rc = Timeout of float | Success of time | Failure of time | Promote of time

type result = {
  executable : string;
  rc : rc;
  test: Test.t;
  log: string;
}

(* The runner may not be installed *)
type 'a output =
  | Skipped
  | Done of 'a

type job = {
  executable : string;
  test : Test.t;
  run : timeout:float -> env:string array -> sources:string -> result output;
}

val jobs : timetool:string -> executables:string list -> promote:bool -> Test.t -> job list

end
