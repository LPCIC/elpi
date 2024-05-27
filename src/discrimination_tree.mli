type cell
type path = cell array

val mkConstant : safe:bool -> data:int -> arity:int -> cell
val mkPrimitive : Elpi_util.Util.CData.t -> cell
val mkVariable : cell
val mkLam : cell
val mkInputMode : cell
val mkOutputMode : cell
val mkListTailVariable : cell
val mkListHead : cell
val mkListEnd : cell
val mkPathEnd : cell

module Trie : sig
  type 'a t
  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
  val show : (Format.formatter -> 'a -> unit) -> 'a t -> string
end

type 'a data
type 'a t

val index : 'a t -> path -> 'a -> time:int -> 'a t
val max_path : 'a t -> int
val max_depths : 'a t -> int array

val empty_dt : 'b list -> 'a t

val retrieve : path -> 'a t -> 'a list

(***********************************************************)
(* Printers                                                *)
(***********************************************************)

val pp_cell : Format.formatter -> cell -> unit
val show_cell : cell -> string

val pp_path : Format.formatter -> path -> unit
val show_path : path -> string

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
  val isPathEnd : cell -> bool
end