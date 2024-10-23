type cell
module Path : sig
  type t
  val pp : Format.formatter -> t -> unit
  val get : t -> int -> cell
  type builder
  val get_builder_pos : builder -> int
  val make : int -> cell -> builder
  val emit : builder -> cell -> unit
  val stop : builder -> t
  val of_list : cell list -> t
end

val mkConstant : safe:bool -> data:int -> arity:int -> cell
val mkPrimitive : Elpi_util.Util.CData.t -> cell
val mkVariable : cell
val mkLam : cell
val mkInputMode : cell
val mkOutputMode : cell
val mkListTailVariable : cell
val mkListTailVariableUnif : cell
val mkListHead : cell
val mkListEnd : cell
val mkPathEnd : cell

type 'a t

(** [index dt path value ~time] returns a new discrimination tree starting from [dt]
      where [value] is added wrt its [path]. [~time] is used as a priority
      marker between two rules.

    A rule with a given [~time] has higher priority on other rules with lower [~time]

    @note: in the elpi runtime, there are no two rule having the same [~time]
*)
val index : 'a t -> max_list_length:int -> Path.t -> 'a -> 'a t

val max_path : 'a t -> int
val max_list_length : 'a t -> int
val max_depths : 'a t -> int array

val empty_dt : 'b list -> 'a t

(** [retrive path dt] Retrives all values in a discrimination tree [dt] from a given path [p].

  The retrival algorithm performs a light unification between [p] and the 
  nodes in the discrimination tree. This light unification takes care of
  unification variables that can be either in the path or in the nodes of [dt]

  The returned list of values are sorted wrt to the order in which values are
  added in the tree: given two rules r_1 and r_2 with same path, if r_1
  has been added at time [t] and r_2 been added at time [t+1] then
  r_2 will appear before r_1 in the final result
*)
val retrieve : ('a -> 'a -> int) -> Path.t -> 'a t -> 'a Bl.scan

val replace : ('a -> bool) -> 'a -> 'a t -> 'a t
val remove  : ('a -> bool) -> 'a t -> 'a t

(***********************************************************)
(* Printers                                                *)
(***********************************************************)

val pp_cell : Format.formatter -> cell -> unit
val show_cell : cell -> string

val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
val show : (Format.formatter -> 'a -> unit) -> 'a t -> string

(***********************************************************)
(* Internal stuff used mainly for unit tests               *)
(***********************************************************)

module Internal: sig
  val kConstant : int
  val kPrimitive : int
  val kVariable : int
  val kOther : int

  val k_of : cell -> int
  val arity_of : cell -> int
  val data_of : cell -> int

  val isVariable : cell -> bool
  val isLam : cell -> bool
  val isInput : cell -> bool
  val isOutput : cell -> bool
  val isListHead : cell -> bool
  val isListEnd : cell -> bool
  val isListTailVariable : cell -> bool
  val isListTailVariableUnif : cell -> bool
  val isPathEnd : cell -> bool
end