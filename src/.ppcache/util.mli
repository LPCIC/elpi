(*f81b6f53e85d7c289fb4bc5c47b7848e424f39c1 *src/util.mli *)
#1 "src/util.mli"
module type Show  =
  sig
    type t[@@deriving show]
    val pp :
      Ppx_deriving_runtime_proxy.Format.formatter -> t -> Ppx_deriving_runtime_proxy.unit
    val show : t -> Ppx_deriving_runtime_proxy.string
  end
module type Show1  =
  sig
    type 'a t[@@deriving show]
    val pp :
      (Ppx_deriving_runtime_proxy.Format.formatter ->
         'a -> Ppx_deriving_runtime_proxy.unit)
        ->
        Ppx_deriving_runtime_proxy.Format.formatter ->
          'a t -> Ppx_deriving_runtime_proxy.unit
    val show :
      (Ppx_deriving_runtime_proxy.Format.formatter ->
         'a -> Ppx_deriving_runtime_proxy.unit)
        -> 'a t -> Ppx_deriving_runtime_proxy.string
  end
module type Show2  =
  sig
    type ('a, 'b) t[@@deriving show]
    val pp :
      (Ppx_deriving_runtime_proxy.Format.formatter ->
         'a -> Ppx_deriving_runtime_proxy.unit)
        ->
        (Ppx_deriving_runtime_proxy.Format.formatter ->
           'b -> Ppx_deriving_runtime_proxy.unit)
          ->
          Ppx_deriving_runtime_proxy.Format.formatter ->
            ('a, 'b) t -> Ppx_deriving_runtime_proxy.unit
    val show :
      (Ppx_deriving_runtime_proxy.Format.formatter ->
         'a -> Ppx_deriving_runtime_proxy.unit)
        ->
        (Ppx_deriving_runtime_proxy.Format.formatter ->
           'b -> Ppx_deriving_runtime_proxy.unit)
          -> ('a, 'b) t -> Ppx_deriving_runtime_proxy.string
  end
module Map :
sig
  module type S  =
    sig include Map.S include Show1 with type 'a t :=  'a t end
  module type OrderedType  =
    sig include Map.OrderedType include Show with type  t :=  t end
  module Make : functor (Ord : OrderedType) -> S with type  key =  Ord.t
end
module Set :
sig
  module type S  = sig include Set.S include Show with type  t :=  t end
  module type OrderedType  =
    sig include Set.OrderedType include Show with type  t :=  t end
  module Make : functor (Ord : OrderedType) -> S with type  elt =  Ord.t
end
module Int :
sig
  type t = int
  val compare : t -> t -> int
  include Show with type  t :=  int
end
module String :
sig include module type of String include Show with type  t :=  string end
module StrMap : Map.S with type  key =  string
module IntMap : Map.S with type  key =  int
module StrSet : Set.S with type  elt =  string
module IntSet : Set.S with type  elt =  int
module PtrMap :
sig
  type 'a t
  val empty : unit -> 'a t
  val is_empty : 'a t -> bool
  val find : 'block -> 'a t -> 'a
  val add : 'block -> 'a -> 'a t -> 'a t
  val remove : 'block -> 'a t -> 'a t
  val filter : ('block -> 'a -> bool) -> 'a t -> 'a t
  include Show1 with type 'a t :=  'a t
end
module Digest :
sig include module type of Digest include Show with type  t :=  t end
module Hashtbl :
sig
  include module type of Hashtbl
  include Show2 with type ('a,'b) t :=  ('a, 'b) t
end
module Loc :
sig
  type t =
    {
    source_name: string ;
    source_start: int ;
    source_stop: int ;
    line: int ;
    line_starts_at: int }[@@deriving (show, eq, ord)]
  val pp :
    Ppx_deriving_runtime_proxy.Format.formatter -> t -> Ppx_deriving_runtime_proxy.unit
  val show : t -> Ppx_deriving_runtime_proxy.string
  val equal : t -> t -> Ppx_deriving_runtime_proxy.bool
  val compare : t -> t -> Ppx_deriving_runtime_proxy.int
  val initial : string -> t
end
val smart_map : ('a -> 'a) -> 'a list -> 'a list
val uniqq : 'a list -> 'a list
val for_all2 : ('a -> 'a -> bool) -> 'a list -> 'a list -> bool
val for_all3b :
  ('a -> 'a -> bool -> bool) ->
    'a list -> 'a list -> bool list -> bool -> bool
val remove_from_list : 'a -> 'a list -> 'a list
val map_exists : ('a -> 'b option) -> 'a list -> 'b option
val map_filter : ('a -> 'b option) -> 'a list -> 'b list
val map_acc :
  ('acc -> 'a -> ('acc * 'b)) -> 'acc -> 'a list -> ('acc * 'b list)
val map_acc2 :
  ('acc -> 'a -> 'b -> ('acc * 'c)) ->
    'acc -> 'a list -> 'b list -> ('acc * 'c list)
val map_acc3 :
  ('acc -> 'a -> 'b -> 'd -> ('acc * 'c)) ->
    'acc -> 'a list -> 'b list -> 'd list -> ('acc * 'c list)
val partition_i : (int -> 'a -> bool) -> 'a list -> ('a list * 'a list)
val partition_i : (int -> 'a -> bool) -> 'a list -> ('a list * 'a list)
val fold_left2i :
  (int -> 'acc -> 'x -> 'y -> 'acc) -> 'acc -> 'x list -> 'y list -> 'acc
val uniq : 'a list -> 'a list
val option_get : ?err:string -> 'a option -> 'a
val option_map : ('a -> 'b) -> 'a option -> 'b option
val pp_option :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a option -> unit
val option_mapacc :
  ('acc -> 'a -> ('acc * 'b)) -> 'acc -> 'a option -> ('acc * 'b option)
val option_iter : ('a -> unit) -> 'a option -> unit
module UUID :
sig
  type t[@@deriving (eq, ord, show)]
  val equal : t -> t -> Ppx_deriving_runtime_proxy.bool
  val compare : t -> t -> Ppx_deriving_runtime_proxy.int
  val pp :
    Ppx_deriving_runtime_proxy.Format.formatter -> t -> Ppx_deriving_runtime_proxy.unit
  val show : t -> Ppx_deriving_runtime_proxy.string
  val hash : t -> int
  val make : unit -> t
  module Htbl : Hashtbl.S with type  key =  t
end
val pplist :
  ?max:int ->
    ?boxed:bool ->
      (Format.formatter -> 'a -> unit) ->
        ?pplastelem:(Format.formatter -> 'a -> unit) ->
          string -> Format.formatter -> 'a list -> unit
val pp_int : Format.formatter -> int -> unit
val pp_string : Format.formatter -> string -> unit
val pp_pair :
  (Format.formatter -> 'a -> unit) ->
    (Format.formatter -> 'b -> unit) -> Format.formatter -> ('a * 'b) -> unit
val pp_option :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a option -> unit
type 'a spaghetti_printer
val mk_spaghetti_printer : unit -> 'a spaghetti_printer
val set_spaghetti_printer :
  'a spaghetti_printer -> (Format.formatter -> 'a -> unit) -> unit
val pp_spaghetti : 'a spaghetti_printer -> Format.formatter -> 'a -> unit
val show_spaghetti : 'a spaghetti_printer -> 'a -> string
val pp_spaghetti_any :
  (UUID.t * Obj.t) spaghetti_printer ->
    id:UUID.t -> Format.formatter -> 'a -> unit
module Fork :
sig
  type 'a local_ref = 'a ref
  val new_local : 'a -> 'a local_ref
  type process =
    {
    exec: 'a 'b . ('a -> 'b) -> 'a -> 'b ;
    get: 'a . 'a local_ref -> 'a ;
    set: 'a . 'a local_ref -> 'a -> unit }
  val fork : unit -> process
end
val error : ?loc:Loc.t -> string -> 'a
val anomaly : ?loc:Loc.t -> string -> 'a
val type_error : ?loc:Loc.t -> string -> 'a
val warn : ?loc:Loc.t -> string -> unit
val printf : ('a, Format.formatter, unit) format -> 'a
val eprintf : ('a, Format.formatter, unit) format -> 'a
val set_warn : (?loc:Loc.t -> string -> unit) -> unit
val set_error : (?loc:Loc.t -> string -> 'a) -> unit
val set_anomaly : (?loc:Loc.t -> string -> 'a) -> unit
val set_type_error : (?loc:Loc.t -> string -> 'a) -> unit
val set_std_formatter : Format.formatter -> unit
val set_err_formatter : Format.formatter -> unit
val set_formatters_maxcols : int -> unit
val set_formatters_maxbox : int -> unit
module CData :
sig
  type t[@@deriving (show, eq, ord)]
  val pp :
    Ppx_deriving_runtime_proxy.Format.formatter -> t -> Ppx_deriving_runtime_proxy.unit
  val show : t -> Ppx_deriving_runtime_proxy.string
  val equal : t -> t -> Ppx_deriving_runtime_proxy.bool
  val compare : t -> t -> Ppx_deriving_runtime_proxy.int
  type 'a data_declaration =
    {
    data_name: string ;
    data_pp: Format.formatter -> 'a -> unit ;
    data_compare: 'a -> 'a -> int ;
    data_hash: 'a -> int ;
    data_hconsed: bool }
  type 'a cdata = private
    {
    cin: 'a -> t ;
    isc: t -> bool ;
    cout: t -> 'a ;
    name: string }
  val declare : 'a data_declaration -> 'a cdata
  val hash : t -> int
  val name : t -> string
  val hcons : t -> t
  val morph1 : 'a cdata -> ('a -> 'a) -> t -> t
  val ty2 : 'a cdata -> t -> t -> bool
  val morph2 : 'a cdata -> ('a -> 'a -> 'a) -> t -> t -> t
  val map : 'a cdata -> 'b cdata -> ('a -> 'b) -> t -> t
end

