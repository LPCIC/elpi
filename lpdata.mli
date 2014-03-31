val debug : bool

(* External data: partial instantiate declare with a print and equality function
 * to get a factory for a type *)
module C : sig
  type data
  val declare : ('a -> string) -> ('a -> 'a -> bool) -> 'a -> data
  val print : data -> string
  val equal : data -> data -> bool
end

(* Immutable arrays with fast sub and append TODO *)
module IA : sig
  include BIA.S

  (* TODO: evaluate rope like structure with compression on get *)
  val append : 'a t -> 'a t -> 'a t
  val cons : 'a -> 'a t -> 'a t
end

val on_buffer : (Format.formatter -> 'a -> unit) -> 'a -> string

module LP :
  sig
    type var = int
    type level = int
    type name = string
    type arity = int
    type data =
        Uv of var * level * arity
      | Con of name * level
      | DB of int
      | Bin of int * data
      | Tup of data IA.t
      | Ext of C.data
    val mkApp : data -> data IA.t -> int -> int -> data
    val fixTup : data IA.t -> data
    val pr_var : int -> string
    val equal : data -> data -> bool
    val fresh_names : int -> int -> string list
    val print : ?ctx:string list -> data -> string
    val printf : string list -> Format.formatter -> data -> unit
    val fold : (data -> 'a -> 'a) -> data -> 'a -> 'a
    val map : (data -> data) -> data -> data
    val max_uv : data -> var -> var
    val fold_map :
      (data -> 'a -> data * 'a) -> data -> 'a -> data * 'a
    type program = clause list
    and clause = int * head * premise list
    and head = data
    and premise =
        Atom of data
      | Impl of data * premise
      | Pi of name * premise
    and goal = premise
    val map_premise : (data -> data) -> premise -> premise
    val fold_premise : (data -> 'a -> 'a) -> premise -> 'a -> 'a
    val fold_map_premise :
      (data -> 'a -> data * 'a) -> premise -> 'a -> premise * 'a
    val parse_program : string -> program
    val parse_goal : string -> goal
    val print_premise : premise -> string
    val print_premisef : name list -> Format.formatter -> premise -> unit
    val print_goal : premise -> string
    val print_goalf : Format.formatter -> premise -> unit
    val print_head : ?ctx:string list -> data -> name
    val print_clause : clause -> string
    val print_clausef : Format.formatter -> clause -> unit
    val print_program : program -> string
    val print_programf : Format.formatter -> program -> unit
  end
