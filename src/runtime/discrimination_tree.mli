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

(** This is for: unification variables, discard *)
val mkVariable : cell

(** This is for: 
  - lambda-abstractions: DT does not perform HO unification, nor βη-redex unif
  - too big terms: if the path of the goal is bigger then the max path in the
                   rules, each term is replaced with this constructor. Note that
                   we do not use mkVariable, since in input mode a variable
                   cannot be unified with non-flex terms. In DT, mkAny is
                   unified with anything
*)
val mkAny : cell
val mkInputMode : cell
val mkOutputMode : cell

(** This is for the last term of opened lists.

  If the list ends is [1,2|X] == Cons (CData'1',Cons(CData'2',Arg (_, _)))

  The corresponding path will be: ListHead, Primitive, Primitive,
  ListTailVariable

  ListTailVariable is considered as a variable, and if it appears in a goal in
  input position, it cannot be unified with non-flex terms
*)
val mkListTailVariable : cell

(** This is used for capped lists.

  If the length of the maximal list in the rules of a predicate is N, then any
  (sub-)list in the goal longer then N encodes the first N elements in the path
  and the last are replaced with ListTailVariableUnif.

  The main difference with ListTailVariable is that DT will unify this symbol to
  both flex and non-flex terms in the path of rules
*)
val mkListTailVariableUnif : cell
val mkListHead : cell
val mkListEnd : cell

(** This is padding used to fill the array in paths and indicate the retrieve
      function to stop making unification. 

    Note that the array for the path has a length which is doubled each time the
    terms in it are larger then the forseen length. Each time the array is
    doubled, the new cells are filled with PathEnd.
*)
val mkPathEnd : cell

type 'a t

(** [index dt ~max_list_length path value] returns a new discrimination tree
      starting from [dt] where [value] is added wrt its [path].

    [max_list_length] is provided and used to update (if needed) the length of
    the longest list in the received path.
*)
val index : 'a t -> max_list_length:int -> Path.t -> 'a -> 'a t

val max_path : 'a t -> int
val max_list_length : 'a t -> int
val max_depths : 'a t -> int array

val empty_dt : 'b list -> 'a t

(** [retrive cmp path dt] Retrives all values in a discrimination tree [dt] from
    a given path [p].

  The retrival algorithm performs a light unification between [p] and the nodes
  in the discrimination tree. This light unification takes care of unification
  variables that can be either in the path or in the nodes of [dt]

  The returned list is sorted wrt [cmp] so that rules are given in the expected
  order
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
  val isAny : cell -> bool
  val isInput : cell -> bool
  val isOutput : cell -> bool
  val isListHead : cell -> bool
  val isListEnd : cell -> bool
  val isListTailVariable : cell -> bool
  val isListTailVariableUnif : cell -> bool
  val isPathEnd : cell -> bool
end