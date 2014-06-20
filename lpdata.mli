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

val superscript : int -> string
val subscript : int -> string

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
  val map : ('a -> 'b) -> 'a t -> 'b t
  val mapi : (int -> 'a -> 'a) -> 'a t -> 'a t
  val fold_map : ('a -> 'b -> 'c * 'b) -> 'a t -> 'b -> 'c t * 'b
  val fold : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val fold2 : ('a -> 'c -> 'b -> 'b) -> 'a t -> 'c t -> 'b -> 'b
  val for_all : ('a -> bool) -> 'a t -> bool
  val exists : ('a -> bool) -> 'a t -> bool
  val for_alli : (int -> 'a -> bool) -> 'a t -> bool
  val for_all2 : ('a -> 'b -> bool) -> 'a t -> 'b t -> bool
  val filter : ('a -> bool) -> 'a t -> 'a t
  val filter_acc : ('a -> 'b -> bool * 'b) -> 'a t -> 'b -> 'a t * 'b
  val to_list : 'a t -> 'a list
  val of_list : 'a list -> 'a t
  val append : 'a t -> 'a t -> 'a t
  val cons : 'a -> 'a t -> 'a t
  val uniq : ('a -> 'a -> bool) -> 'a t -> bool
  val rev : 'a t -> 'a t
end

module Name : sig
  type t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val make : string -> t
  val to_string : t -> string
end

module LP : sig
  type var = int
  type level = int
  type name = Name.t
  type data
  type appkind = [ `Regular | `Rev | `Flex | `Frozen ]

  type kind_of_data = private
    | Uv of var * level
    | Con of name * level (* level < 0 has to be considered as 0 *)
    | DB of int
    | Bin of int * data
    | App of data L.t
    | Seq of data L.t * data
    | Nil
    | Ext of C.data
    | VApp of appkind * data * data (* VApp(hd,args) : args is a list *)

  val look : data -> kind_of_data
  val kool : kind_of_data -> data
  
  val mkUv : var -> level -> data
  val mkCon : string -> level -> data
  val mkDB : int -> data
  val mkBin : int -> data -> data
  val mkApp : data L.t -> data
  val mkVApp : appkind -> data -> data -> data
  val mkExt : C.data -> data
  val mkSeq : data L.t -> data -> data
  val mkNil : data

  val mkAppv : data -> data L.t -> int -> int -> data
  val fixApp : data L.t -> data

  val equal : data -> data -> bool
  val compare : data -> data -> int
  
  val isDB : int -> data -> bool

  val collect_Uv : data -> data list

  module CN : sig
    type t
    val equal : t -> t -> bool
    val make : ?float:[ `Here | `Begin | `End ] -> ?existing:bool -> string -> t
    val fresh : unit -> t
    val pp : Format.formatter -> t -> unit
    val to_string : t -> string
  end

  type key = Key of data | Flex
  type program = annot_clause list
  and annot_clause = int * key * clause * CN.t
  and clause = premise
  and premise = data
  and goal = premise
  
  val mkAtom : data -> premise
  val mkAtomBiUnif : data -> data -> premise
  val mkAtomBiCustom : string -> data -> premise
  val mkAtomBiCut : premise
  val mkConj : premise L.t -> premise
  val mkImpl : premise -> premise -> premise
  val mkPi : int -> premise -> premise
  val mkSigma : int -> premise -> premise
  val mkDelay : data -> premise -> premise

  val eq_clause : annot_clause -> annot_clause -> bool
  val cmp_clause : annot_clause -> annot_clause -> int

  type builtin = BIUnif of data * data | BICustom of string * data | BICut
  type kind_of_premise =
      Atom of data
    | AtomBI of builtin
    | Conj of premise L.t
    | Impl of clause * premise
    | Pi of int * premise
    | Sigma of int * premise
    | Delay of data * premise
    | Resume of data * premise

  val look_premise : data -> kind_of_premise

  val isConj : premise -> bool
  val destConj : premise -> premise list
  val isAtom : premise -> bool
  val destAtom : premise -> data

  val key_of : premise -> key

  val map_premise : (data -> data) -> premise -> premise
  val mapi_premise : (int -> data -> data) -> int -> premise -> premise

  val collect_Uv_premise : premise -> data list
  val collect_hv_premise : premise -> data list

  val parse_program : ?ontop:program -> string -> program
  val parse_goal : string -> goal
  val parse_data : string -> data

  val mkFreshCon : string -> int -> data

  val prf_data : string list -> Format.formatter -> data -> unit
  val prf_data_only : string list -> Format.formatter -> data -> unit
  val prf_premise : string list -> Format.formatter -> premise -> unit
  val prf_goal : string list -> Format.formatter -> goal -> unit
  val prf_clause : string list -> Format.formatter -> clause -> unit
  val prf_program : ?compact:bool -> Format.formatter -> program -> unit
  
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
  val freeze_uv : LP.var -> subst -> LP.data * subst
  val is_frozen : LP.data -> bool
  val set_sub : LP.var -> LP.data -> subst -> subst
  val set_sub_con : LP.level -> LP.data -> subst -> subst
  val top : subst -> int
  val raise_top : int -> subst -> subst
  
  val prf_subst : Format.formatter -> subst -> unit
  val string_of_subst : subst -> string
end

module Red : sig
  val lift : ?from:int -> int -> LP.data -> LP.data
  val whd : LP.data -> Subst.subst -> LP.data * Subst.subst
  val nf : LP.data -> Subst.subst -> LP.data * Subst.subst
end

