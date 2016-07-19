type identifier = string

val next_ident_away : identifier -> identifier list -> identifier

val lift_subscript   : identifier -> identifier

type label
type reference

type env
type constant_body
type ('a,'b) prec_declaration

type module_path
type mod_bound_id

module Intmap : Map.S with type key = int

module Intset : Set.S with type elt = int

module Uriset : Set.S with type elt = NUri.uri

module Idset : Set.S with type elt=identifier

module Refmap : Map.S with type key = NReference.reference

module Stringmap : Map.S with type key = string

module Pp_control : sig
 val with_output_to : out_channel -> Format.formatter
 val get_margin: unit -> int option
end

val iterate : ('a -> 'a) -> int -> 'a -> 'a
val list_skipn : int -> 'a list -> 'a list
val list_split_at : int -> 'a list -> 'a list*'a list
val list_chop : int -> 'a list -> 'a list * 'a list
val list_firstn : int -> 'a list -> 'a list
val list_iter_i :  (int -> 'a -> unit) -> 'a list -> unit
val list_lastn : int -> 'a list -> 'a list
val array_map2 : ('a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array
val array_for_all : ('a -> bool) -> 'a array -> bool
val array_fold_right_i :
  (int -> 'b -> 'a -> 'a) -> 'b array -> 'a -> 'a
val identity : 'a -> 'a
val interval : int -> int -> int list
val map_status: 's -> ('s -> 'a -> 's * 'b) -> 'a list -> 's * 'b list
val array_map_status: 's -> ('s -> 'a -> 's * 'b) -> 'a array -> 's * 'b array
val array_mapi_status :
 's -> ('s -> int -> 'a -> 's * 'b) -> 'a array -> 's * 'b array

type std_ppcmds
val (++) : std_ppcmds -> std_ppcmds -> std_ppcmds
val spc : unit -> std_ppcmds
val str : string -> std_ppcmds
val mt : unit -> std_ppcmds
val v : int -> std_ppcmds -> std_ppcmds
val hv : int -> std_ppcmds -> std_ppcmds
val hov : int -> std_ppcmds -> std_ppcmds
val int : int -> std_ppcmds
val stras : int * string -> std_ppcmds
val fnl : unit -> std_ppcmds
val prlist_with_sep_status :
 'a -> (unit -> std_ppcmds) -> ('a -> 'b -> 'a * std_ppcmds) -> 'b list ->
   'a * std_ppcmds
val prlist_with_sep :
   (unit -> std_ppcmds) -> ('b -> std_ppcmds) -> 'b list -> std_ppcmds
val pr_id : identifier -> std_ppcmds
val prlist : ('a -> std_ppcmds) -> 'a list -> std_ppcmds
val prlist_strict :  ('a -> std_ppcmds) -> 'a list -> std_ppcmds
val prvect_with_sep :
   (unit -> std_ppcmds) -> ('a -> std_ppcmds) -> 'a array -> std_ppcmds
val prvect_with_sep_status :
 's -> (unit -> std_ppcmds) -> ('s -> 'a -> 's * std_ppcmds) -> 'a array -> 's * std_ppcmds
val prvect : ('a -> std_ppcmds) -> 'a array -> std_ppcmds
val prvecti : (int -> 'a -> std_ppcmds) -> 'a array -> std_ppcmds
val prvecti_status :
 's -> ('s -> int -> 'a -> 's * std_ppcmds) -> 'a array -> 's * std_ppcmds
val list_map_i : (int -> 'a -> 'b) -> int -> 'a list -> 'b list
val list_map_i_status :
 's -> ('s -> int -> 'a -> 's * 'b) -> int -> 'a list -> 's * 'b list

val pp_with : Format.formatter -> std_ppcmds -> unit
