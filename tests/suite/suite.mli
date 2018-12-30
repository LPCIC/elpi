
module Test : sig

type fname = string

type expectation =
  | Success
  | Failure
  | Output of fname

val declare :
  (*name*)string ->
  description:string ->
  ?source_elpi:fname ->
  ?source_teyjus:fname ->
  ?deps_teyjus:fname list ->
  ?typecheck:bool ->
  ?input:fname -> 
  ?expectation:expectation -> 
  ?outside_llam:bool ->
  category:string ->
  unit -> unit

type t = {
  name : string;
  description : string;
  category: string;
  source_elpi : fname option;
  source_teyjus : fname option;
  deps_teyjus : fname list;
  typecheck : bool;
  input : fname option;
  expectation : expectation;
  outside_llam : bool;
}

val get : (name:string -> bool) -> t list

val names : unit -> (string * string list) list (* grouped by category *)

end

module Runner : sig

type time = {
  time : float;
  walltime : float;
  mem : int;
}
type rc = Timeout of float | Success of time | Failure of time

type result = {
  executable : string;
  rc : rc;
  test: Test.t;
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

val jobs : timetool:string -> executables:string list -> Test.t -> job list

end
