(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

(******************** list ******************)

val smart_map : ('a -> 'a) -> 'a list -> 'a list
(* tail rec when the two lists have len 1; raises no exception. *)
val uniqq: 'a list -> 'a list
val for_all2 : ('a -> 'a -> bool) -> 'a list -> 'a list -> bool
val for_all3b : ('a -> 'a -> bool -> bool) -> 'a list -> 'a list -> bool list -> bool -> bool
(*uses physical equality and calls anomaly if the element is not in the list*)
val remove_from_list : 'a -> 'a list -> 'a list
(* returns Some t where f x = Some t for the first x in the list s.t.
   f x <> None; returns None if for every x in the list, f x = None *)
val map_exists : ('a -> 'b option) -> 'a list -> 'b option
val map_filter : ('a -> 'b option) -> 'a list -> 'b list
val map_acc : ('acc -> 'a -> 'acc * 'b) -> 'acc -> 'a list -> 'acc * 'b list
val partition_i : (int -> 'a -> bool) -> 'a list -> 'a list * 'a list
val fold_left2i :
  (int -> 'acc -> 'x -> 'y -> 'acc) -> 'acc -> 'x list -> 'y list -> 'acc
val uniq : 'a list -> 'a list

(******************** option ******************)

val option_get : ?err:string -> 'a option -> 'a
val option_map : ('a -> 'b) -> 'a option -> 'b option
val pp_option :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a option -> unit
val option_mapacc :
  ('acc -> 'a -> 'acc * 'b) -> 'acc -> 'a option -> 'acc * 'b option

(***************** Unique ID ****************)

module UUID : sig

 type t
 val compare : t -> t -> int
 val equal : t -> t -> bool
 val hash : t -> int
 val pp : Format.formatter -> t -> unit
 val show : t -> string

 val make : unit -> t

 module Htbl : Hashtbl.S with type key = t

end

(******************** printing ******************)

val pplist : ?max:int -> ?boxed:bool ->
  (Format.formatter -> 'a -> unit) ->
  ?pplastelem:(Format.formatter -> 'a -> unit) -> string ->
    Format.formatter -> 'a list -> unit
val pp_int : Format.formatter -> int -> unit
val pp_pair :
  (Format.formatter -> 'a -> unit) ->
  (Format.formatter -> 'b -> unit) ->
    Format.formatter -> 'a * 'b -> unit

(* for open types *)
type 'a extensible_printer
val mk_extensible_printer : unit -> 'a extensible_printer
val extend_printer :
  'a extensible_printer ->
  (Format.formatter -> 'a -> [`Printed | `Passed]) ->
     unit
val pp_extensible :
  'a extensible_printer -> Format.formatter -> 'a -> unit
val pp_extensible_any :
  (UUID.t * Obj.t) extensible_printer -> id:UUID.t -> Format.formatter -> 'a -> unit

(******************** runtime is reentrant ******************)

(* of course we don't fork, we just swap sets of local refs *)
module Fork : sig

  type 'a local_ref = 'a ref

  val new_local : 'a -> 'a local_ref

  type process = {
    (* To run a function f in the child process, no effect from f
     * is visible after exec, but running f again trough the same exec
     * (in the same process) sees such effects *)
    exec : 'a 'b. ('a -> 'b) -> 'a -> 'b;

    (* To get/set values from the memory of the child *)
    get : 'a. 'a local_ref -> 'a;
    set : 'a. 'a local_ref -> 'a -> unit
  }
  
  val fork : unit -> process

end

(******************** errors ******************)

(* A regular error *)
val error : string -> 'a
(* An invariant is broken, i.e. a bug *)
val anomaly : string -> 'a
(* If we type check the program, then these are anomalies *)
val type_error : string -> 'a
(* A non fatal warning *)
val warn : string -> unit


val set_warn : (string -> unit) -> unit
val set_error : (string -> 'a) -> unit
val set_anomaly : (string -> 'a) -> unit
val set_type_error : (string -> 'a) -> unit

(* ****************** external data *****************)

module CData : sig
  type t

  type 'a data_declaration = {
    data_name : string;
    data_pp : Format.formatter -> 'a -> unit;
    data_eq : 'a -> 'a -> bool;
    data_hash : 'a -> int;
  }

  type 'a cdata = { cin : 'a -> t; isc : t -> bool; cout: t -> 'a }

  val declare : 'a data_declaration -> 'a cdata
  val pp : Format.formatter -> t -> unit
  val show : t -> string
  val equal : t -> t -> bool
  val hash : t -> int
  val name : t -> string

  val morph1 : 'a cdata -> ('a -> 'a) -> t -> t

  val ty2 : 'a cdata -> t -> t -> bool
  val morph2 : 'a cdata -> ('a -> 'a -> 'a) -> t -> t -> t
  
  val map : 'a cdata -> 'b cdata -> ('a -> 'b) -> t -> t
end

(* Object oriented state for quotations: each quotation can declare
 * a component that is carried by all other quotations *)
module ExtState : sig

  type t

  type 'a set = t -> 'a -> t
  type 'a update = t -> ('a -> 'a) -> t
  type 'a get = t -> 'a
  type 'a init = unit -> 'a

  val declare_extension : string -> 'a init -> ('a get * 'a set * 'a update)
  
  val init : unit -> t 

end
