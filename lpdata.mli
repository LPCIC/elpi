(* elpi: embedded lambda prolog interpreter                                  *)
(* copyright: 2014 - Enrico Tassi <enrico.tassi@inria.fr>                    *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

(* External data: partial instantiate declare with a print and equality function
 * to get a factory for a type *)
module C : sig
  type data
  val declare : ('a -> string) -> ('a -> 'a -> bool) -> ('a -> data) * (data -> bool) * (data -> 'a)
  val print : data -> string
  val equal : data -> data -> bool
end

val mkString : string -> C.data
val isString : C.data -> bool
val getString : C.data -> string

module L : sig
  type 'a t
  val empty : 'a t
  val singl : 'a -> 'a t
  val init : int -> (int -> 'a) -> 'a t
  val get : int -> 'a t -> 'a
  val len : 'a t -> int
  val sub : int -> int -> 'a t -> 'a t
  val tl : 'a t -> 'a t
  val hd : 'a t -> 'a
  val map : ('a -> 'a) -> 'a t -> 'a t
  val mapi : (int -> 'a -> 'a) -> 'a t -> 'a t
  val fold_map : ('a -> 'b -> 'a * 'b) -> 'a t -> 'b -> 'a t * 'b
  val fold : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val fold2 : ('a -> 'c -> 'b -> 'b) -> 'a t -> 'c t -> 'b -> 'b
  val for_all : ('a -> bool) -> 'a t -> bool
  val for_alli : (int -> 'a -> bool) -> 'a t -> bool
  val for_all2 : ('a -> 'b -> bool) -> 'a t -> 'b t -> bool
  val filter : ('a -> bool) -> 'a t -> 'a t
  val to_list : 'a t -> 'a list
  val of_list : 'a list -> 'a t
  val append : 'a t -> 'a t -> 'a t
  val cons : 'a -> 'a t -> 'a t
  val uniq : ('a -> 'a -> bool) -> 'a t -> bool
end

module LP : sig
  type var = int
  type level = int
  type name = string
  type data

  type kind_of_data = private
    | Uv of var * level
    | Con of name * level
    | DB of int
    | Bin of int * data
    | App of data L.t
    | Seq of data L.t * data
    | Nil
    | Ext of C.data

  val look : data -> kind_of_data
  val kool : kind_of_data -> data
  
  val mkUv : var -> level -> data
  val mkCon : name -> level -> data
  val mkDB : int -> data
  val mkBin : int -> data -> data
  val mkApp : data L.t -> data
  val mkExt : C.data -> data
  val mkSeq : data L.t -> data -> data
  val mkNil : data

  val mkAppv : data -> data L.t -> int -> int -> data
  val fixApp : data L.t -> data

  val equal : data -> data -> bool
  
  val fold : (data -> 'a -> 'a) -> data -> 'a -> 'a
  val map : (data -> data) -> data -> data
  val fold_map :
    int -> (int -> data -> 'a -> data * 'a) -> data -> 'a -> data * 'a

  val max_uv : data -> var -> var
  val isDB : int -> data -> bool

  type key = Key of data | Flex
  type builtin = BIUnif of data * data | BICustom of string * data | BICut
  type program = annot_clause list
  and annot_clause = int * data list * key * clause
  and clause = premise
  and premise =
      Atom of data
    | AtomBI of builtin
    | Conj of premise list
    | Impl of clause * premise
    | Pi of int * premise
    | Sigma of int * premise
    | Not of premise
  and goal = premise

  val key_of : premise -> key

  val map_premise : (data -> data) -> premise -> premise
  val fold_premise : (data -> 'a -> 'a) -> premise -> 'a -> 'a
  val fold_map_premise :
    int -> (int -> data -> 'a -> data * 'a) -> premise -> 'a -> premise * 'a

  val parse_program : string -> program
  val parse_goal : string -> goal
  val parse_data : string -> data

  val prf_data : name list -> Format.formatter -> data -> unit
  val prf_premise : name list -> Format.formatter -> premise -> unit
  val prf_goal : name list -> Format.formatter -> goal -> unit
  val prf_clause : name list -> Format.formatter -> clause -> unit
  val prf_program : Format.formatter -> program -> unit
  
  val string_of_data : ?ctx:string list -> data -> string
  val string_of_premise : premise -> string
  val string_of_goal : premise -> string
  val string_of_clause : clause -> string
  val string_of_program : program -> string
end

module Subst : sig
  type subst

  (* takes the highest Uv in the goal *)
  val empty : int -> subst
  val apply_subst : subst -> LP.data -> LP.data
  val apply_subst_goal : subst -> LP.goal -> LP.goal
  val fresh_uv : LP.level -> subst -> LP.data * subst
  val set_sub : int -> LP.data -> subst -> subst
  val top : subst -> int
  val raise_top : int -> subst -> subst
  
  val prf_subst : Format.formatter -> subst -> unit
  val string_of_subst : subst -> string
end

module Red : sig
  val lift : ?from:int -> int -> LP.data -> LP.data
  val beta_under : int -> LP.data -> LP.data list -> LP.data
  val whd : Subst.subst -> LP.data -> LP.data * Subst.subst
  val nf : Subst.subst -> LP.data -> LP.data
end

