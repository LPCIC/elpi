module CSig : sig

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Missing pervasive types from OCaml stdlib *)

type ('a, 'b) union = Inl of 'a | Inr of 'b
(** Union type *)

type 'a until = Stop of 'a | Cont of 'a
(** Used for browsable-until structures. *)

type (_, _) eq = Refl : ('a, 'a) eq

module type SetS =
sig
    type elt
    type t
    val empty: t
    val is_empty: t -> bool
    val mem: elt -> t -> bool
    val add: elt -> t -> t
    val singleton: elt -> t
    val remove: elt -> t -> t
    val union: t -> t -> t
    val inter: t -> t -> t
    val diff: t -> t -> t
    val compare: t -> t -> int
    val equal: t -> t -> bool
    val subset: t -> t -> bool
    val iter: (elt -> unit) -> t -> unit
    val fold: (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all: (elt -> bool) -> t -> bool
    val exists: (elt -> bool) -> t -> bool
    val filter: (elt -> bool) -> t -> t
    val partition: (elt -> bool) -> t -> t * t
    val cardinal: t -> int
    val elements: t -> elt list
    val min_elt: t -> elt
    val max_elt: t -> elt
    val choose: t -> elt
    val split: elt -> t -> t * bool * t
end
(** Redeclaration of OCaml set signature, to preserve compatibility. See OCaml
    documentation for more information. *)

module type EmptyS = sig end

module type MapS =
sig
    type key
    type (+'a) t
    val empty: 'a t
    val is_empty: 'a t -> bool
    val mem: key -> 'a t -> bool
    val add: key -> 'a -> 'a t -> 'a t
    val singleton: key -> 'a -> 'a t
    val remove: key -> 'a t -> 'a t
    val merge:
         (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
    val compare: ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal: ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val iter: (key -> 'a -> unit) -> 'a t -> unit
    val fold: (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val for_all: (key -> 'a -> bool) -> 'a t -> bool
    val exists: (key -> 'a -> bool) -> 'a t -> bool
    val filter: (key -> 'a -> bool) -> 'a t -> 'a t
    val partition: (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
    val cardinal: 'a t -> int
    val bindings: 'a t -> (key * 'a) list
    val min_binding: 'a t -> (key * 'a)
    val max_binding: 'a t -> (key * 'a)
    val choose: 'a t -> (key * 'a)
    val split: key -> 'a t -> 'a t * 'a option * 'a t
    val find: key -> 'a t -> 'a
    val map: ('a -> 'b) -> 'a t -> 'b t
    val mapi: (key -> 'a -> 'b) -> 'a t -> 'b t
end
end = struct

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Missing pervasive types from OCaml stdlib *)

type ('a, 'b) union = Inl of 'a | Inr of 'b
(** Union type *)

type 'a until = Stop of 'a | Cont of 'a
(** Used for browsable-until structures. *)

type (_, _) eq = Refl : ('a, 'a) eq

module type SetS =
sig
    type elt
    type t
    val empty: t
    val is_empty: t -> bool
    val mem: elt -> t -> bool
    val add: elt -> t -> t
    val singleton: elt -> t
    val remove: elt -> t -> t
    val union: t -> t -> t
    val inter: t -> t -> t
    val diff: t -> t -> t
    val compare: t -> t -> int
    val equal: t -> t -> bool
    val subset: t -> t -> bool
    val iter: (elt -> unit) -> t -> unit
    val fold: (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all: (elt -> bool) -> t -> bool
    val exists: (elt -> bool) -> t -> bool
    val filter: (elt -> bool) -> t -> t
    val partition: (elt -> bool) -> t -> t * t
    val cardinal: t -> int
    val elements: t -> elt list
    val min_elt: t -> elt
    val max_elt: t -> elt
    val choose: t -> elt
    val split: elt -> t -> t * bool * t
end
(** Redeclaration of OCaml set signature, to preserve compatibility. See OCaml
    documentation for more information. *)

module type EmptyS = sig end

module type MapS =
sig
    type key
    type (+'a) t
    val empty: 'a t
    val is_empty: 'a t -> bool
    val mem: key -> 'a t -> bool
    val add: key -> 'a -> 'a t -> 'a t
    val singleton: key -> 'a -> 'a t
    val remove: key -> 'a t -> 'a t
    val merge:
         (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
    val compare: ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal: ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val iter: (key -> 'a -> unit) -> 'a t -> unit
    val fold: (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val for_all: (key -> 'a -> bool) -> 'a t -> bool
    val exists: (key -> 'a -> bool) -> 'a t -> bool
    val filter: (key -> 'a -> bool) -> 'a t -> 'a t
    val partition: (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
    val cardinal: 'a t -> int
    val bindings: 'a t -> (key * 'a) list
    val min_binding: 'a t -> (key * 'a)
    val max_binding: 'a t -> (key * 'a)
    val choose: 'a t -> (key * 'a)
    val split: key -> 'a t -> 'a t * 'a option * 'a t
    val find: key -> 'a t -> 'a
    val map: ('a -> 'b) -> 'a t -> 'b t
    val mapi: (key -> 'a -> 'b) -> 'a t -> 'b t
end
end

module Pp = struct
  type std_ppcmds = unit
  let str (s : string) = ()
  let h _ _ = ()
  let v _ _ = ()
  let hv _ _ = ()
  let hov _ _ = ()
  let prlist_with_sep _ _ _ = ()
  let prlist _ _ = ()
  let pr_sequence _ _ = ()
  let prvect_with_sep _ _ _ = ()
  let fnl _ = ()
  let spc _ = ()
  let mt _ = ()
  let pr_comma _ = ()
  let int _ = ()
  let (++) () () = ()
end

module Option : sig 

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Module implementing basic combinators for OCaml option type.
   It tries follow closely the style of OCaml standard library.

   Actually, some operations have the same name as [List] ones:
   they actually are similar considering ['a option] as a type
   of lists with at most one element. *)

exception IsNone

(** [has_some x] is [true] if [x] is of the form [Some y] and [false]
    otherwise.  *)
val has_some : 'a option -> bool

(** Negation of [has_some] *)
val is_empty : 'a option -> bool

(** [equal f x y] lifts the equality predicate [f] to
    option types. That is, if both [x] and [y] are [None] then
    it returns [true], if they are both [Some _] then
    [f] is called. Otherwise it returns [false]. *)
val equal : ('a -> 'a -> bool) -> 'a option -> 'a option -> bool

(** Same as [equal], but with comparison. *)
val compare : ('a -> 'a -> int) -> 'a option -> 'a option -> int

(** Lift a hash to option types. *)
val hash : ('a -> int) -> 'a option -> int

(** [get x] returns [y] where [x] is [Some y].
    @raise IsNone if [x] equals [None]. *)
val get : 'a option -> 'a

(** [make x] returns [Some x]. *)
val make : 'a -> 'a option

(** [init b x] returns [Some x] if [b] is [true] and [None] otherwise. *)
val init : bool -> 'a -> 'a option

(** [flatten x] is [Some y] if [x] is [Some (Some y)] and [None] otherwise. *)
val flatten : 'a option option -> 'a option

(** [append x y] is the first element of the concatenation of [x] and
    [y] seen as lists.  In other words, [append (Some a) y] is [Some
    a], [append None (Some b)] is [Some b], and [append None None] is
    [None]. *)
val append : 'a option -> 'a option -> 'a option


(** {6 "Iterators"} *)

(** [iter f x] executes [f y] if [x] equals [Some y]. It does nothing
    otherwise. *)
val iter : ('a -> unit) -> 'a option -> unit

exception Heterogeneous

(** [iter2 f x y] executes [f z w] if [x] equals [Some z] and [y] equals
    [Some w]. It does nothing if both [x] and [y] are [None].
    @raise Heterogeneous otherwise. *)
val iter2 : ('a -> 'b -> unit) -> 'a option -> 'b option -> unit

(** [map f x] is [None] if [x] is [None] and [Some (f y)] if [x] is [Some y]. *)
val map : ('a -> 'b) -> 'a option -> 'b option

(** [smartmap f x] does the same as [map f x] except that it tries to share
    some memory. *)
val smartmap : ('a -> 'a) -> 'a option -> 'a option

(** [fold_left f a x] is [f a y] if [x] is [Some y], and [a] otherwise. *)
val fold_left : ('b -> 'a -> 'b) -> 'b -> 'a option -> 'b

(** [fold_left2 f a x y] is [f z w] if [x] is [Some z] and [y] is [Some w].
    It is [a] if both [x] and [y] are [None].
    @raise Heterogeneous otherwise. *)
val fold_left2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b option -> 'c option -> 'a

(** [fold_right f x a] is [f y a] if [x] is [Some y], and [a] otherwise. *)
val fold_right : ('a -> 'b -> 'b) -> 'a option -> 'b -> 'b

(** [fold_map f a x] is [a, f y] if [x] is [Some y], and [a] otherwise. *)
val fold_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b option -> 'a * 'c option

(** [cata f e x] is [e] if [x] is [None] and [f a] if [x] is [Some a] *)
val cata : ('a -> 'b) -> 'b -> 'a option -> 'b

(** {6 More Specific Operations} *)

(** [default a x] is [y] if [x] is [Some y] and [a] otherwise. *)
val default : 'a -> 'a option -> 'a

(** [lift] is the same as {!map}. *)
val lift : ('a -> 'b) -> 'a option -> 'b option

(** [lift_right f a x] is [Some (f a y)] if [x] is [Some y], and
    [None] otherwise. *)
val lift_right : ('a -> 'b -> 'c) -> 'a -> 'b option -> 'c option

(** [lift_left f x a] is [Some (f y a)] if [x] is [Some y], and
    [None] otherwise. *)
val lift_left : ('a -> 'b -> 'c) -> 'a option -> 'b -> 'c option

(** [lift2 f x y] is [Some (f z w)] if [x] equals [Some z] and [y] equals
    [Some w]. It is [None] otherwise. *)
val lift2 : ('a -> 'b -> 'c) -> 'a option -> 'b option -> 'c option


(** {6 Operations with Lists} *)

module List : sig
  (** [List.cons x l] equals [y::l] if [x] is [Some y] and [l] otherwise. *)
  val cons : 'a option -> 'a list -> 'a list

  (** [List.flatten l] is the list of all the [y]s such that [l] contains
      [Some y] (in the same order). *)
  val flatten : 'a option list -> 'a list

  val find : ('a -> 'b option) -> 'a list -> 'b option

end

end = struct 

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Module implementing basic combinators for OCaml option type.
   It tries follow closely the style of OCaml standard library.

   Actually, some operations have the same name as [List] ones:
   they actually are similar considering ['a option] as a type
   of lists with at most one element. *)

(** [has_some x] is [true] if [x] is of the form [Some y] and [false]
    otherwise.  *)
let has_some = function
  | None -> false
  | _ -> true

let is_empty = function
| None -> true
| Some _ -> false

(** Lifting equality onto option types. *)
let equal f x y = match x, y with
| None, None -> true
| Some x, Some y -> f x y
| _, _ -> false

let compare f x y = match x, y with
| None, None -> 0
| Some x, Some y -> f x y
| None, Some _ -> -1
| Some _, None -> 1

let hash f = function
| None -> 0
| Some x -> f x

exception IsNone

(** [get x] returns [y] where [x] is [Some y].
    @raise [IsNone] if [x] equals [None]. *)
let get = function
  | Some y -> y
  | _ -> raise IsNone

(** [make x] returns [Some x]. *)
let make x = Some x

(** [init b x] returns [Some x] if [b] is [true] and [None] otherwise. *)
let init b x =
  if b then
    Some x
  else
    None


(** [flatten x] is [Some y] if [x] is [Some (Some y)] and [None] otherwise. *)
let flatten = function
  | Some (Some y) -> Some y
  | _ -> None


(** [append x y] is the first element of the concatenation of [x] and
    [y] seen as lists. *)
let append o1 o2 =
  match o1 with
  | Some _ -> o1
  | None  -> o2


(** {6 "Iterators"} ***)

(** [iter f x] executes [f y] if [x] equals [Some y]. It does nothing
    otherwise. *)
let iter f = function
  | Some y -> f y
  | _ -> ()


exception Heterogeneous

(** [iter2 f x y] executes [f z w] if [x] equals [Some z] and [y] equals
    [Some w]. It does nothing if both [x] and [y] are [None]. And raises
    [Heterogeneous] otherwise. *)
let iter2 f x y =
  match x,y with
  | Some z, Some w -> f z w
  | None,None -> ()
  | _,_ -> raise Heterogeneous

(** [map f x] is [None] if [x] is [None] and [Some (f y)] if [x] is [Some y]. *)
let map f = function
  | Some y -> Some (f y)
  | _ -> None

(** [smartmap f x] does the same as [map f x] except that it tries to share
    some memory. *)
let smartmap f = function
  | Some y as x -> let y' = f y in if y' == y then x else Some y'
  | _ -> None

(** [fold_left f a x] is [f a y] if [x] is [Some y], and [a] otherwise. *)
let fold_left f a = function
  | Some y -> f a y
  | _ -> a

(** [fold_left2 f a x y] is [f z w] if [x] is [Some z] and [y] is [Some w].
    It is [a] if both [x] and [y] are [None]. Otherwise it raises
    [Heterogeneous]. *)
let fold_left2 f a x y =
  match x,y with
  | Some x, Some y -> f a x y
  | None, None -> a
  | _ -> raise Heterogeneous

(** [fold_right f x a] is [f y a] if [x] is [Some y], and [a] otherwise. *)
let fold_right f x a =
  match x with
  | Some y -> f y a
  | _ -> a

(** [fold_map f a x] is [a, f y] if [x] is [Some y], and [a] otherwise. *)
let fold_map f a x =
  match x with
  | Some y -> let a, z = f a y in a, Some z
  | _ -> a, None

(** [cata f a x] is [a] if [x] is [None] and [f y] if [x] is [Some y]. *)
let cata f a = function
  | Some c -> f c
  | None -> a

(** {6 More Specific operations} ***)

(** [default a x] is [y] if [x] is [Some y] and [a] otherwise. *)
let default a = function
  | Some y -> y
  | _ -> a

(** [lift f x] is the same as [map f x]. *)
let lift = map

(** [lift_right f a x] is [Some (f a y)] if [x] is [Some y], and
    [None] otherwise. *)
let lift_right f a = function
  | Some y -> Some (f a y)
  | _ -> None

(** [lift_left f x a] is [Some (f y a)] if [x] is [Some y], and
    [None] otherwise. *)
let lift_left f x a =
  match x with
  | Some y -> Some (f y a)
  | _ -> None

(** [lift2 f x y] is [Some (f z w)] if [x] equals [Some z] and [y] equals
    [Some w]. It is [None] otherwise. *)
let lift2 f x y =
  match x,y with
  | Some z, Some w -> Some (f z w)
  | _,_ -> None



(** {6 Operations with Lists} *)

module List =
 struct
  (** [List.cons x l] equals [y::l] if [x] is [Some y] and [l] otherwise. *)
  let cons x l =
    match x with
    | Some y -> y::l
    | _ -> l

  (** [List.flatten l] is the list of all the [y]s such that [l] contains
      [Some y] (in the same order). *)
  let rec flatten = function
    | x::l -> cons x (flatten l)
    | [] -> []

  let rec find f = function
    |[] -> None
    |h :: t -> match f h with
	 |None -> find f t
	 |x -> x

end

end


module Util = struct

end

module CErrors = struct
  let anomaly ?(label="") _ = assert false
end

module CMap : sig
        
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** {5 Extended version of OCaml's maps} *)

module type OrderedType =
sig
  type t
  val compare : t -> t -> int
end

module type MonadS =
sig
  type +'a t
  val return : 'a -> 'a t
  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
end

module type S = Map.S

module type ExtS =
sig
  include CSig.MapS
  (** The underlying Map library *)

  module Set : CSig.SetS with type elt = key
  (** Sets used by the domain function *)

  val get : key -> 'a t -> 'a
  (** Same as {!find} but fails an assertion instead of raising [Not_found] *)

  val update : key -> 'a -> 'a t -> 'a t
  (** Same as [add], but expects the key to be present, and thus faster.
      @raise Not_found when the key is unbound in the map. *)

  val modify : key -> (key -> 'a -> 'a) -> 'a t -> 'a t
  (** Apply the given function to the binding of the given key.
      @raise Not_found when the key is unbound in the map. *)

  val domain : 'a t -> Set.t
  (** Recover the set of keys defined in the map. *)

  val bind : (key -> 'a) -> Set.t -> 'a t
  (** [bind f s] transform the set [x1; ...; xn] into [x1 := f x1; ...;
      xn := f xn]. *)

  val fold_left : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  (** Alias for {!fold}, to easily track where we depend on fold order. *)

  val fold_right : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  (** Folding keys in decreasing order. *)

  val smartmap : ('a -> 'a) -> 'a t -> 'a t
  (** As [map] but tries to preserve sharing. *)

  val smartmapi : (key -> 'a -> 'a) -> 'a t -> 'a t
  (** As [mapi] but tries to preserve sharing. *)

  val height : 'a t -> int
  (** An indication of the logarithmic size of a map *)

  module Unsafe :
  sig
    val map : (key -> 'a -> key * 'b) -> 'a t -> 'b t
    (** As the usual [map], but also allows modifying the key of a binding.
        It is required that the mapping function [f] preserves key equality,
        i.e.: for all (k : key) (x : 'a), compare (fst (f k x)) k = 0. *)
  end

  module Monad(M : MonadS) :
  sig
    val fold : (key -> 'a -> 'b -> 'b M.t) -> 'a t -> 'b -> 'b M.t
    val fold_left : (key -> 'a -> 'b -> 'b M.t) -> 'a t -> 'b -> 'b M.t
    val fold_right : (key -> 'a -> 'b -> 'b M.t) -> 'a t -> 'b -> 'b M.t
  end
  (** Fold operators parameterized by any monad. *)

end

module Make(M : Map.OrderedType) : ExtS with
  type key = M.t
  and type 'a t = 'a Map.Make(M).t
  and module Set := Set.Make(M)
        
end = struct

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module type OrderedType =
sig
  type t
  val compare : t -> t -> int
end

module type MonadS =
sig
  type +'a t
  val return : 'a -> 'a t
  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
end

module type S = Map.S

module type ExtS =
sig
  include CSig.MapS
  module Set : CSig.SetS with type elt = key
  val get : key -> 'a t -> 'a
  val update : key -> 'a -> 'a t -> 'a t
  val modify : key -> (key -> 'a -> 'a) -> 'a t -> 'a t
  val domain : 'a t -> Set.t
  val bind : (key -> 'a) -> Set.t -> 'a t
  val fold_left : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val fold_right : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val smartmap : ('a -> 'a) -> 'a t -> 'a t
  val smartmapi : (key -> 'a -> 'a) -> 'a t -> 'a t
  val height : 'a t -> int
  module Unsafe :
  sig
    val map : (key -> 'a -> key * 'b) -> 'a t -> 'b t
  end
  module Monad(M : MonadS) :
  sig
    val fold : (key -> 'a -> 'b -> 'b M.t) -> 'a t -> 'b -> 'b M.t
    val fold_left : (key -> 'a -> 'b -> 'b M.t) -> 'a t -> 'b -> 'b M.t
    val fold_right : (key -> 'a -> 'b -> 'b M.t) -> 'a t -> 'b -> 'b M.t
  end
end

module MapExt (M : Map.OrderedType) :
sig
  type 'a map = 'a Map.Make(M).t
  val update : M.t -> 'a -> 'a map -> 'a map
  val modify : M.t -> (M.t -> 'a -> 'a) -> 'a map -> 'a map
  val domain : 'a map -> Set.Make(M).t
  val bind : (M.t -> 'a) -> Set.Make(M).t -> 'a map
  val fold_left : (M.t -> 'a -> 'b -> 'b) -> 'a map -> 'b -> 'b
  val fold_right : (M.t -> 'a -> 'b -> 'b) -> 'a map -> 'b -> 'b
  val smartmap : ('a -> 'a) -> 'a map -> 'a map
  val smartmapi : (M.t -> 'a -> 'a) -> 'a map -> 'a map
  val height : 'a map -> int
  module Unsafe :
  sig
    val map : (M.t -> 'a -> M.t * 'b) -> 'a map -> 'b map
  end
  module Monad(MS : MonadS) :
  sig
    val fold : (M.t -> 'a -> 'b -> 'b MS.t) -> 'a map -> 'b -> 'b MS.t
    val fold_left : (M.t -> 'a -> 'b -> 'b MS.t) -> 'a map -> 'b -> 'b MS.t
    val fold_right : (M.t -> 'a -> 'b -> 'b MS.t) -> 'a map -> 'b -> 'b MS.t
  end
end =
struct
  (** This unsafe module is a way to access to the actual implementations of
      OCaml sets and maps without reimplementing them ourselves. It is quite
      dubious that these implementations will ever be changed... Nonetheless,
      if this happens, we can still implement a less clever version of [domain].
  *)

  type 'a map = 'a Map.Make(M).t
  type set = Set.Make(M).t

  type 'a _map =
  | MEmpty
  | MNode of 'a map * M.t * 'a * 'a map * int

  type _set =
  | SEmpty
  | SNode of set * M.t * set * int

  let map_prj : 'a map -> 'a _map = Obj.magic
  let map_inj : 'a _map -> 'a map = Obj.magic
  let set_prj : set -> _set = Obj.magic
  let set_inj : _set -> set = Obj.magic

  let rec update k v (s : 'a map) : 'a map = match map_prj s with
  | MEmpty -> raise Not_found
  | MNode (l, k', v', r, h) ->
    let c = M.compare k k' in
    if c < 0 then
      let l' = update k v l in
      if l == l' then s
      else map_inj (MNode (l', k', v', r, h))
    else if c = 0 then
      if v' == v then s
      else map_inj (MNode (l, k', v, r, h))
    else
      let r' = update k v r in
      if r == r' then s
      else map_inj (MNode (l, k', v', r', h))

  let rec modify k f (s : 'a map) : 'a map = match map_prj s with
  | MEmpty -> raise Not_found
  | MNode (l, k', v, r, h) ->
    let c = M.compare k k' in
    if c < 0 then
      let l' = modify k f l in
      if l == l' then s
      else map_inj (MNode (l', k', v, r, h))
    else if c = 0 then
      let v' = f k' v in
      if v' == v then s
      else map_inj (MNode (l, k', v', r, h))
    else
      let r' = modify k f r in
      if r == r' then s
      else map_inj (MNode (l, k', v, r', h))

  let rec domain (s : 'a map) : set = match map_prj s with
  | MEmpty -> set_inj SEmpty
  | MNode (l, k, _, r, h) ->
    set_inj (SNode (domain l, k, domain r, h))
  (** This function is essentially identity, but OCaml current stdlib does not
      take advantage of the similarity of the two structures, so we introduce
      this unsafe loophole. *)

  let rec bind f (s : set) : 'a map = match set_prj s with
  | SEmpty -> map_inj MEmpty
  | SNode (l, k, r, h) ->
    map_inj (MNode (bind f l, k, f k, bind f r, h))
  (** Dual operation of [domain]. *)

  let rec fold_left f (s : 'a map) accu = match map_prj s with
  | MEmpty -> accu
  | MNode (l, k, v, r, h) ->
    let accu = f k v (fold_left f l accu) in
    fold_left f r accu

  let rec fold_right f (s : 'a map) accu = match map_prj s with
  | MEmpty -> accu
  | MNode (l, k, v, r, h) ->
    let accu = f k v (fold_right f r accu) in
    fold_right f l accu

  let rec smartmap f (s : 'a map) = match map_prj s with
  | MEmpty -> map_inj MEmpty
  | MNode (l, k, v, r, h) ->
    let l' = smartmap f l in
    let r' = smartmap f r in
    let v' = f v in
    if l == l' && r == r' && v == v' then s
    else map_inj (MNode (l', k, v', r', h))

  let rec smartmapi f (s : 'a map) = match map_prj s with
  | MEmpty -> map_inj MEmpty
  | MNode (l, k, v, r, h) ->
    let l' = smartmapi f l in
    let r' = smartmapi f r in
    let v' = f k v in
    if l == l' && r == r' && v == v' then s
    else map_inj (MNode (l', k, v', r', h))

  let height s = match map_prj s with
  | MEmpty -> 0
  | MNode (_, _, _, _, h) -> h

  module Unsafe =
  struct

    let rec map f (s : 'a map) : 'b map = match map_prj s with
    | MEmpty -> map_inj MEmpty
    | MNode (l, k, v, r, h) ->
      let (k, v) = f k v in
      map_inj (MNode (map f l, k, v, map f r, h))

  end

  module Monad(M : MonadS) =
  struct

    open M

    let rec fold_left f s accu = match map_prj s with
    | MEmpty -> return accu
    | MNode (l, k, v, r, h) ->
      fold_left f l accu >>= fun accu ->
      f k v accu >>= fun accu ->
      fold_left f r accu

    let rec fold_right f s accu = match map_prj s with
    | MEmpty -> return accu
    | MNode (l, k, v, r, h) ->
      fold_right f r accu >>= fun accu ->
      f k v accu >>= fun accu ->
      fold_right f l accu

    let fold = fold_left

  end

end

module Make(M : Map.OrderedType) =
struct
  include Map.Make(M)
  include MapExt(M)
  let get k m = try find k m with Not_found -> assert false
end
end


module Int : sig

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** A native integer module with usual utility functions. *)

type t = int

external equal : t -> t -> bool = "%eq"

external compare : t -> t -> int = "caml_int_compare"

val hash : t -> int

module Set : Set.S with type elt = t
module Map : CMap.ExtS with type key = t and module Set := Set

module List : sig
  val mem : int -> int list -> bool
  val assoc : int -> (int * 'a) list -> 'a
  val mem_assoc : int -> (int * 'a) list -> bool
  val remove_assoc : int -> (int * 'a) list -> (int * 'a) list
end

module PArray :
sig
  type 'a t
  (** Persistent, auto-resizable arrays. The [get] and [set] functions never
      fail whenever the index is between [0] and [Sys.max_array_length - 1]. *)
  val empty : int -> 'a t
  (** The empty array, with a given starting size. *)
  val get : 'a t -> int -> 'a option
  (** Get a value at the given index. Returns [None] if undefined. *)
  val set : 'a t -> int -> 'a option -> 'a t
  (** Set/unset a value at the given index. *)
end

module PMap :
sig
  type key = int
  type 'a t
  val empty : 'a t
  val is_empty : 'a t -> bool
  val mem : key -> 'a t -> bool
  val add : key -> 'a -> 'a t -> 'a t
  val singleton : key -> 'a -> 'a t
  val remove : key -> 'a t -> 'a t
(*   val merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t *)
(*   val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int *)
(*   val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool *)
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val for_all : (key -> 'a -> bool) -> 'a t -> bool
  val exists : (key -> 'a -> bool) -> 'a t -> bool
(*   val filter : (key -> 'a -> bool) -> 'a t -> 'a t *)
(*   val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t *)
(*   val cardinal : 'a t -> int *)
(*   val bindings : 'a t -> (key * 'a) list *)
(*   val min_binding : 'a t -> key * 'a *)
(*   val max_binding : 'a t -> key * 'a *)
(*   val choose : 'a t -> key * 'a *)
(*   val split : key -> 'a t -> 'a t * 'a option * 'a t *)
  val find : key -> 'a t -> 'a
(*   val map : ('a -> 'b) -> 'a t -> 'b t *)
(*   val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t *)
  val domain : 'a t -> Set.t
(*   val cast : 'a t -> 'a Map.t *)
end
(** This is a (partial) implementation of a [Map] interface on integers, except
    that it internally uses persistent arrays. This ensures O(1) accesses in
    non-backtracking cases. It is thus better suited for zero-starting,
    contiguous keys, or otherwise a lot of space will be empty. To keep track of
    the present keys, a binary tree is also used, so that adding a key is
    still logarithmic. It is therefore essential that most of the operations
    are accesses and not add/removes. *)

end = struct

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type t = int

external equal : int -> int -> bool = "%eq"

external compare : int -> int -> int = "caml_int_compare"

let hash i = i land 0x3FFFFFFF

module Self =
struct
  type t = int
  let compare = compare
end

module Set = Set.Make(Self)
module Map =
struct
  include CMap.Make(Self)

  type 'a map = 'a CMap.Make(Self).t

  type 'a _map =
  | MEmpty
  | MNode of 'a map * int * 'a * 'a map * int

  let map_prj : 'a map -> 'a _map = Obj.magic

  let rec find i s = match map_prj s with
  | MEmpty -> raise Not_found
  | MNode (l, k, v, r, h) ->
    if i < k then find i l
    else if i = k then v
    else find i r
end

module List = struct
  let mem = List.memq
  let assoc = List.assq
  let mem_assoc = List.mem_assq
  let remove_assoc = List.remove_assq
end

let min (i : int) j = if i < j then i else j

(** Utility function *)
let rec next from upto =
  if from < upto then next (2 * from + 1) upto
  else from


module PArray =
struct

  type 'a t = 'a data ref
  and 'a data =
  | Root of 'a option array
  | DSet of int * 'a option * 'a t

  let empty n = ref (Root (Array.make n None))

  let rec rerootk t k = match !t with
  | Root _ -> k ()
  | DSet (i, v, t') ->
    let next () = match !t' with
    | Root a as n ->
      let v' = Array.unsafe_get a i in
      let () = Array.unsafe_set a i v in
      let () = t := n in
      let () = t' := DSet (i, v', t) in
      k ()
    | DSet _ -> assert false
    in
    rerootk t' next

  let reroot t = rerootk t (fun () -> ())

  let get t i =
  let () = assert (0 <= i) in
  match !t with
  | Root a ->
    if Array.length a <= i then None
    else Array.unsafe_get a i
  | DSet _ ->
    let () = reroot t in
    match !t with
    | Root a ->
      if Array.length a <= i then None
      else Array.unsafe_get a i
    | DSet _ -> assert false

  let set t i v =
    let () = assert (0 <= i) in
    let () = reroot t in
    match !t with
    | DSet _ -> assert false
    | Root a as n ->
      let len = Array.length a in
      if i < len then
        let old = Array.unsafe_get a i in
        if old == v then t
        else
          let () = Array.unsafe_set a i v in
          let res = ref n in
          let () = t := DSet (i, old, res) in
          res
      else match v with
      | None -> t (** Nothing to do! *)
      | Some _ -> (** we must resize *)
        let nlen = next len (succ i) in
        let nlen = min nlen Sys.max_array_length in
        let () = assert (i < nlen) in
        let a' = Array.make nlen None in
        let () = Array.blit a 0 a' 0 len in
        let () = Array.unsafe_set a' i v in
        let res = ref (Root a') in
        let () = t := DSet (i, None, res) in
        res

end

module PMap =
struct

  type key = int

  (** Invariants:

    1. an empty map is always [Empty].
    2. the set of the [Map] constructor remembers the present keys.
  *)
  type 'a t = Empty | Map of Set.t * 'a PArray.t

  let empty = Empty

  let is_empty = function
  | Empty -> true
  | Map _ -> false

  let singleton k x =
    let len = next 19 (k + 1) in
    let len = min Sys.max_array_length len in
    let v = PArray.empty len in
    let v = PArray.set v k (Some x) in
    let s = Set.singleton k in
    Map (s, v)

  let add k x = function
  | Empty -> singleton k x
  | Map (s, v) ->
    let s = match PArray.get v k with
    | None -> Set.add k s
    | Some _ -> s
    in
    let v = PArray.set v k (Some x) in
    Map (s, v)

  let remove k = function
  | Empty -> Empty
  | Map (s, v) ->
    let s = Set.remove k s in
    if Set.is_empty s then Empty
    else
      let v = PArray.set v k None in
      Map (s, v)

  let mem k = function
  | Empty -> false
  | Map (_, v) ->
    match PArray.get v k with
    | None -> false
    | Some _ -> true

  let find k = function
  | Empty -> raise Not_found
  | Map (_, v) ->
    match PArray.get v k with
    | None -> raise Not_found
    | Some x -> x

  let iter f = function
  | Empty -> ()
  | Map (s, v) ->
    let iter k = match PArray.get v k with
    | None -> ()
    | Some x -> f k x
    in
    Set.iter iter s

  let fold f m accu = match m with
  | Empty -> accu
  | Map (s, v) ->
    let fold k accu = match PArray.get v k with
    | None -> accu
    | Some x -> f k x accu
    in
    Set.fold fold s accu

  let exists f m = match m with
  | Empty -> false
  | Map (s, v) ->
    let exists k = match PArray.get v k with
    | None -> false
    | Some x -> f k x
    in
    Set.exists exists s

  let for_all f m = match m with
  | Empty -> true
  | Map (s, v) ->
    let for_all k = match PArray.get v k with
    | None -> true
    | Some x -> f k x
    in
    Set.for_all for_all s

(*
  let cast = function
  | Empty -> Map.empty
  | Map (s, v) ->
    let bind k = match PArray.get v k with
    | None -> assert false
    | Some x -> x
    in
    Map.bind bind s
*)

  let domain = function
  | Empty -> Set.empty
  | Map (s, _) -> s

end

end

module CList : sig

(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

type 'a cmp = 'a -> 'a -> int
type 'a eq = 'a -> 'a -> bool

(** Module type [S] is the one from OCaml Stdlib. *)
module type S = module type of List

module type ExtS =
sig
  include S

  val compare : 'a cmp -> 'a list cmp
  (** Lexicographic order on lists. *)

  val equal : 'a eq -> 'a list eq
  (** Lifts equality to list type. *)

  val is_empty : 'a list -> bool
  (** Checks whether a list is empty *)

  val init : int -> (int -> 'a) -> 'a list
  (** [init n f] constructs the list [f 0; ... ; f (n - 1)]. *)

  val mem_f : 'a eq -> 'a -> 'a list -> bool
  (* Same as [List.mem], for some specific equality *)

  val add_set : 'a eq -> 'a -> 'a list -> 'a list
  (** [add_set x l] adds [x] in [l] if it is not already there, or returns [l]
      otherwise. *)

  val eq_set : 'a eq -> 'a list eq
  (** Test equality up to permutation (but considering multiple occurrences) *)

  val intersect : 'a eq -> 'a list -> 'a list -> 'a list
  val union : 'a eq -> 'a list -> 'a list -> 'a list
  val unionq : 'a list -> 'a list -> 'a list
  val subtract : 'a eq -> 'a list -> 'a list -> 'a list
  val subtractq : 'a list -> 'a list -> 'a list

  val interval : int -> int -> int list
  (** [interval i j] creates the list [[i; i + 1; ...; j]], or [[]] when 
      [j <= i]. *)

  val make : int -> 'a -> 'a list
  (** [make n x] returns a list made of [n] times [x]. Raise
      [Invalid_argument "List.make"] if [n] is negative. *)

  val assign : 'a list -> int -> 'a -> 'a list
  (** [assign l i x] set the [i]-th element of [l] to [x], starting from [0]. *)

  val distinct : 'a list -> bool
  (** Return [true] if all elements of the list are distinct. *)

  val distinct_f : 'a cmp -> 'a list -> bool

  val duplicates : 'a eq -> 'a list -> 'a list
  (** Return the list of unique elements which appear at least twice. Elements
      are kept in the order of their first appearance. *)

  val filter2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> 'a list * 'b list
  val map_filter : ('a -> 'b option) -> 'a list -> 'b list
  val map_filter_i : (int -> 'a -> 'b option) -> 'a list -> 'b list

  val filter_with : bool list -> 'a list -> 'a list
  (** [filter_with b a] selects elements of [a] whose corresponding element in
      [b] is [true]. Raise [Invalid_argument _] when sizes differ. *)

  val smartmap : ('a -> 'a) -> 'a list -> 'a list
  (** [smartmap f [a1...an] = List.map f [a1...an]] but if for all i
    [f ai == ai], then [smartmap f l == l] *)

  val map_left : ('a -> 'b) -> 'a list -> 'b list
  (** As [map] but ensures the left-to-right order of evaluation. *)

  val map_i : (int -> 'a -> 'b) -> int -> 'a list -> 'b list
  (** As [map] but with the index, which starts from [0]. *)

  val map2_i :
    (int -> 'a -> 'b -> 'c) -> int -> 'a list -> 'b list -> 'c list
  val map3 :
    ('a -> 'b -> 'c -> 'd) -> 'a list -> 'b list -> 'c list -> 'd list
  val map4 : ('a -> 'b -> 'c -> 'd -> 'e) -> 'a list -> 'b list -> 'c list ->
    'd list -> 'e list
  val filteri : (int -> 'a -> bool) -> 'a list -> 'a list
  val partitioni : (int -> 'a -> bool) -> 'a list -> 'a list * 'a list

  val smartfilter : ('a -> bool) -> 'a list -> 'a list
  (** [smartfilter f [a1...an] = List.filter f [a1...an]] but if for all i
    [f ai = true], then [smartfilter f l == l] *)

  val extend : bool list -> 'a -> 'a list -> 'a list
(** [extend l a [a1..an]] assumes that the number of [true] in [l] is [n];
    it extends [a1..an] by inserting [a] at the position of [false] in [l] *)
  val count : ('a -> bool) -> 'a list -> int

  val index : 'a eq -> 'a -> 'a list -> int
  (** [index] returns the 1st index of an element in a list (counting from 1). *)

  val index0 : 'a eq -> 'a -> 'a list -> int
  (** [index0] behaves as [index] except that it starts counting at 0. *)

  val iteri :  (int -> 'a -> unit) -> 'a list -> unit
  (** As [iter] but with the index argument (starting from 0). *)

  val fold_left_until : ('c -> 'a -> 'c CSig.until) -> 'c -> 'a list -> 'c
  (** acts like [fold_left f acc s] while [f] returns
      [Cont acc']; it stops returning [c] as soon as [f] returns [Stop c]. *)

  val fold_right_i :  (int -> 'a -> 'b -> 'b) -> int -> 'a list -> 'b -> 'b
  val fold_left_i :  (int -> 'a -> 'b -> 'a) -> int -> 'a -> 'b list -> 'a
  val fold_right_and_left :
      ('a -> 'b -> 'b list -> 'a) -> 'b list -> 'a -> 'a
  val fold_left3 : ('a -> 'b -> 'c -> 'd -> 'a) -> 'a -> 'b list -> 'c list -> 'd list -> 'a
  val for_all_i : (int -> 'a -> bool) -> int -> 'a list -> bool
  val except : 'a eq -> 'a -> 'a list -> 'a list
  val remove : 'a eq -> 'a -> 'a list -> 'a list

  val remove_first : ('a -> bool) -> 'a list -> 'a list
  (** Remove the first element satisfying a predicate, or raise [Not_found] *)

  val extract_first : ('a -> bool) -> 'a list -> 'a list * 'a
  (** Remove and return the first element satisfying a predicate,
      or raise [Not_found] *)

  val insert : ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list
  (** Insert at the (first) position so that if the list is ordered wrt to the
      total order given as argument, the order is preserved *)

  val for_all2eq : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  val sep_last : 'a list -> 'a * 'a list

  val find_map : ('a -> 'b option) -> 'a list -> 'b
  (** Returns the first element that is mapped to [Some _]. Raise [Not_found] if
      there is none. *)

  val uniquize : 'a list -> 'a list
  (** Return the list of elements without duplicates.
      This is the list unchanged if there was none. *)

  val sort_uniquize : 'a cmp -> 'a list -> 'a list
  (** Return a sorted and de-duplicated version of a list,
      according to some comparison function. *)

  val merge_uniq : 'a cmp -> 'a list -> 'a list -> 'a list
  (** Merge two sorted lists and preserves the uniqueness property. *)

  val subset : 'a list -> 'a list -> bool

  val chop : int -> 'a list -> 'a list * 'a list
  (** [chop i l] splits [l] into two lists [(l1,l2)] such that
      [l1++l2=l] and [l1] has length [i].  It raises [Failure] when [i]
      is negative or greater than the length of [l] *)

  exception IndexOutOfRange
  val goto: int -> 'a list -> 'a list * 'a list
  (** [goto i l] splits [l] into two lists [(l1,l2)] such that
      [(List.rev l1)++l2=l] and [l1] has length [i].  It raises
      [IndexOutOfRange] when [i] is negative or greater than the
      length of [l]. *)


  val split_when : ('a -> bool) -> 'a list -> 'a list * 'a list
  val split3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list
  val firstn : int -> 'a list -> 'a list
  val last : 'a list -> 'a
  val lastn : int -> 'a list -> 'a list
  val skipn : int -> 'a list -> 'a list
  val skipn_at_least : int -> 'a list -> 'a list

  val addn : int -> 'a -> 'a list -> 'a list
  (** [addn n x l] adds [n] times [x] on the left of [l]. *)

  val prefix_of : 'a eq -> 'a list -> 'a list -> bool
  (** [prefix_of l1 l2] returns [true] if [l1] is a prefix of [l2], [false]
      otherwise. *)

  val drop_prefix : 'a eq -> 'a list -> 'a list -> 'a list
  (** [drop_prefix p l] returns [t] if [l=p++t] else return [l]. *)

  val drop_last : 'a list -> 'a list

  val map_append : ('a -> 'b list) -> 'a list -> 'b list
  (** [map_append f [x1; ...; xn]] returns [(f x1)@(f x2)@...@(f xn)]. *)

  val map_append2 : ('a -> 'b -> 'c list) -> 'a list -> 'b list -> 'c list
  (** As [map_append]. Raises [Invalid_argument _] if the two lists don't have 
      the same length. *)

  val share_tails : 'a list -> 'a list -> 'a list * 'a list * 'a list

  val fold_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list
  (** [fold_map f e_0 [l_1...l_n] = e_n,[k_1...k_n]]
    where [(e_i,k_i)=f e_{i-1} l_i] *)

  val fold_map' : ('b -> 'a -> 'c * 'a) -> 'b list -> 'a -> 'c list * 'a
  val map_assoc : ('a -> 'b) -> ('c * 'a) list -> ('c * 'b) list
  val assoc_f : 'a eq -> 'a -> ('a * 'b) list -> 'b
  val remove_assoc_f : 'a eq -> 'a -> ('a * 'b) list -> ('a * 'b) list
  val mem_assoc_f : 'a eq -> 'a -> ('a * 'b) list -> bool

  val cartesian : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  (** A generic cartesian product: for any operator (**),
    [cartesian (**) [x1;x2] [y1;y2] = [x1**y1; x1**y2; x2**y1; x2**y1]],
    and so on if there are more elements in the lists. *)

  val cartesians : ('a -> 'b -> 'b) -> 'b -> 'a list list -> 'b list
  (** [cartesians] is an n-ary cartesian product: it iterates
    [cartesian] over a list of lists.  *)

  val combinations : 'a list list -> 'a list list
  (** combinations [[a;b];[c;d]] returns [[a;c];[a;d];[b;c];[b;d]] *)

  val combine3 : 'a list -> 'b list -> 'c list -> ('a * 'b * 'c) list

  val cartesians_filter :
    ('a -> 'b -> 'b option) -> 'b -> 'a list list -> 'b list
  (** Keep only those products that do not return None *)

  val factorize_left : 'a eq -> ('a * 'b) list -> ('a * 'b list) list

  module type MonoS = sig
    type elt
    val equal : elt list -> elt list -> bool
    val mem : elt -> elt list -> bool
    val assoc : elt -> (elt * 'a) list -> 'a
    val mem_assoc : elt -> (elt * 'a) list -> bool
    val remove_assoc : elt -> (elt * 'a) list -> (elt * 'a) list
    val mem_assoc_sym : elt -> ('a * elt) list -> bool
  end
end

include ExtS

end = struct


(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

type 'a cmp = 'a -> 'a -> int
type 'a eq = 'a -> 'a -> bool

module type S = module type of List

module type ExtS =
sig
  include S
  val compare : 'a cmp -> 'a list cmp
  val equal : 'a eq -> 'a list eq
  val is_empty : 'a list -> bool
  val init : int -> (int -> 'a) -> 'a list
  val mem_f : 'a eq -> 'a -> 'a list -> bool
  val add_set : 'a eq -> 'a -> 'a list -> 'a list
  val eq_set : 'a eq -> 'a list -> 'a list -> bool
  val intersect : 'a eq -> 'a list -> 'a list -> 'a list
  val union : 'a eq -> 'a list -> 'a list -> 'a list
  val unionq : 'a list -> 'a list -> 'a list
  val subtract : 'a eq -> 'a list -> 'a list -> 'a list
  val subtractq : 'a list -> 'a list -> 'a list
  val interval : int -> int -> int list
  val make : int -> 'a -> 'a list
  val assign : 'a list -> int -> 'a -> 'a list
  val distinct : 'a list -> bool
  val distinct_f : 'a cmp -> 'a list -> bool
  val duplicates : 'a eq -> 'a list -> 'a list
  val filter2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> 'a list * 'b list
  val map_filter : ('a -> 'b option) -> 'a list -> 'b list
  val map_filter_i : (int -> 'a -> 'b option) -> 'a list -> 'b list
  val filter_with : bool list -> 'a list -> 'a list
  val smartmap : ('a -> 'a) -> 'a list -> 'a list
  val map_left : ('a -> 'b) -> 'a list -> 'b list
  val map_i : (int -> 'a -> 'b) -> int -> 'a list -> 'b list
  val map2_i :
    (int -> 'a -> 'b -> 'c) -> int -> 'a list -> 'b list -> 'c list
  val map3 :
    ('a -> 'b -> 'c -> 'd) -> 'a list -> 'b list -> 'c list -> 'd list
  val map4 :
    ('a -> 'b -> 'c -> 'd -> 'e) -> 'a list -> 'b list -> 'c list -> 'd list -> 'e list
  val filteri :
    (int -> 'a -> bool) -> 'a list -> 'a list
  val partitioni :
    (int -> 'a -> bool) -> 'a list -> 'a list * 'a list
  val smartfilter : ('a -> bool) -> 'a list -> 'a list
  val extend : bool list -> 'a -> 'a list -> 'a list
  val count : ('a -> bool) -> 'a list -> int
  val index : 'a eq -> 'a -> 'a list -> int
  val index0 : 'a eq -> 'a -> 'a list -> int
  val iteri :  (int -> 'a -> unit) -> 'a list -> unit
  val fold_left_until : ('c -> 'a -> 'c CSig.until) -> 'c -> 'a list -> 'c
  val fold_right_i :  (int -> 'a -> 'b -> 'b) -> int -> 'a list -> 'b -> 'b
  val fold_left_i :  (int -> 'a -> 'b -> 'a) -> int -> 'a -> 'b list -> 'a
  val fold_right_and_left :
      ('a -> 'b -> 'b list -> 'a) -> 'b list -> 'a -> 'a
  val fold_left3 : ('a -> 'b -> 'c -> 'd -> 'a) -> 'a -> 'b list -> 'c list -> 'd list -> 'a
  val for_all_i : (int -> 'a -> bool) -> int -> 'a list -> bool
  val except : 'a eq -> 'a -> 'a list -> 'a list
  val remove : 'a eq -> 'a -> 'a list -> 'a list
  val remove_first : ('a -> bool) -> 'a list -> 'a list
  val extract_first : ('a -> bool) -> 'a list -> 'a list * 'a
  val insert : ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list
  val for_all2eq : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  val sep_last : 'a list -> 'a * 'a list
  val find_map : ('a -> 'b option) -> 'a list -> 'b
  val uniquize : 'a list -> 'a list
  val sort_uniquize : 'a cmp -> 'a list -> 'a list
  val merge_uniq : ('a -> 'a -> int) -> 'a list -> 'a list -> 'a list
  val subset : 'a list -> 'a list -> bool
  val chop : int -> 'a list -> 'a list * 'a list
  exception IndexOutOfRange
  val goto : int -> 'a list -> 'a list * 'a list
  val split_when : ('a -> bool) -> 'a list -> 'a list * 'a list
  val split3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list
  val firstn : int -> 'a list -> 'a list
  val last : 'a list -> 'a
  val lastn : int -> 'a list -> 'a list
  val skipn : int -> 'a list -> 'a list
  val skipn_at_least : int -> 'a list -> 'a list
  val addn : int -> 'a -> 'a list -> 'a list
  val prefix_of : 'a eq -> 'a list -> 'a list -> bool
  val drop_prefix : 'a eq -> 'a list -> 'a list -> 'a list
  val drop_last : 'a list -> 'a list
  val map_append : ('a -> 'b list) -> 'a list -> 'b list
  val map_append2 : ('a -> 'b -> 'c list) -> 'a list -> 'b list -> 'c list
  val share_tails : 'a list -> 'a list -> 'a list * 'a list * 'a list
  val fold_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list
  val fold_map' : ('b -> 'a -> 'c * 'a) -> 'b list -> 'a -> 'c list * 'a
  val map_assoc : ('a -> 'b) -> ('c * 'a) list -> ('c * 'b) list
  val assoc_f : 'a eq -> 'a -> ('a * 'b) list -> 'b
  val remove_assoc_f : 'a eq -> 'a -> ('a * 'b) list -> ('a * 'b) list
  val mem_assoc_f : 'a eq -> 'a -> ('a * 'b) list -> bool
  val cartesian : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val cartesians : ('a -> 'b -> 'b) -> 'b -> 'a list list -> 'b list
  val combinations : 'a list list -> 'a list list
  val combine3 : 'a list -> 'b list -> 'c list -> ('a * 'b * 'c) list
  val cartesians_filter :
    ('a -> 'b -> 'b option) -> 'b -> 'a list list -> 'b list
  val factorize_left : 'a eq -> ('a * 'b) list -> ('a * 'b list) list

  module type MonoS = sig
    type elt
    val equal : elt list -> elt list -> bool
    val mem : elt -> elt list -> bool
    val assoc : elt -> (elt * 'a) list -> 'a
    val mem_assoc : elt -> (elt * 'a) list -> bool
    val remove_assoc : elt -> (elt * 'a) list -> (elt * 'a) list
    val mem_assoc_sym : elt -> ('a * elt) list -> bool
  end

end

include List

(** Tail-rec implementation of usual functions. This is a well-known trick used
    in, for instance, ExtLib and Batteries. *)

type 'a cell = {
  head : 'a;
  mutable tail : 'a list;
}

external cast : 'a cell -> 'a list = "%identity"

let rec map_loop f p = function
| [] -> ()
| x :: l ->
  let c = { head = f x; tail = [] } in
  p.tail <- cast c;
  map_loop f c l

let map f = function
| [] -> []
| x :: l ->
  let c = { head = f x; tail = [] } in
  map_loop f c l;
  cast c

let rec map2_loop f p l1 l2 = match l1, l2 with
| [], [] -> ()
| x :: l1, y :: l2 ->
  let c = { head = f x y; tail = [] } in
  p.tail <- cast c;
  map2_loop f c l1 l2
| _ -> invalid_arg "List.map2"

let map2 f l1 l2 = match l1, l2 with
| [], [] -> []
| x :: l1, y :: l2 ->
  let c = { head = f x y; tail = [] } in
  map2_loop f c l1 l2;
  cast c
| _ -> invalid_arg "List.map2"

let rec append_loop p tl = function
| [] -> p.tail <- tl
| x :: l ->
  let c = { head = x; tail = [] } in
  p.tail <- cast c;
  append_loop c tl l

let append l1 l2 = match l1 with
| [] -> l2
| x :: l ->
  let c = { head = x; tail = [] } in
  append_loop c l2 l;
  cast c

let rec copy p = function
| [] -> p
| x :: l ->
  let c = { head = x; tail = [] } in
  p.tail <- cast c;
  copy c l

let rec init_loop len f p i =
  if Int.equal i len then ()
  else
    let c = { head = f i; tail = [] } in
    p.tail <- cast c;
    init_loop len f c (succ i)

let init len f =
  if len < 0 then invalid_arg "List.init"
  else if Int.equal len 0 then []
  else
    let c = { head = f 0; tail = [] } in
    init_loop len f c 1;
    cast c

let rec concat_loop p = function
| [] -> ()
| x :: l -> concat_loop (copy p x) l

let concat l =
  let dummy = { head = Obj.magic 0; tail = [] } in
  concat_loop dummy l;
  dummy.tail

let flatten = concat

let rec split_loop p q = function
| [] -> ()
| (x, y) :: l ->
  let cl = { head = x; tail = [] } in
  let cr = { head = y; tail = [] } in
  p.tail <- cast cl;
  q.tail <- cast cr;
  split_loop cl cr l

let split = function
| [] -> [], []
| (x, y) :: l ->
  let cl = { head = x; tail = [] } in
  let cr = { head = y; tail = [] } in
  split_loop cl cr l;
  (cast cl, cast cr)

let rec combine_loop p l1 l2 = match l1, l2 with
| [], [] -> ()
| x :: l1, y :: l2 ->
  let c = { head = (x, y); tail = [] } in
  p.tail <- cast c;
  combine_loop c l1 l2
| _ -> invalid_arg "List.combine"

let combine l1 l2 = match l1, l2 with
| [], [] -> []
| x :: l1, y :: l2 ->
  let c = { head = (x, y); tail = [] } in
  combine_loop c l1 l2;
  cast c
| _ -> invalid_arg "List.combine"

let rec filter_loop f p = function
| [] -> ()
| x :: l ->
  if f x then
    let c = { head = x; tail = [] } in
    let () = p.tail <- cast c in
    filter_loop f c l
  else
    filter_loop f p l

let filter f l =
  let c = { head = Obj.magic 0; tail = [] } in
  filter_loop f c l;
  c.tail

(** FIXME: Already present in OCaml 4.00 *)

let rec map_i_loop f i p = function
| [] -> ()
| x :: l ->
  let c = { head = f i x; tail = [] } in
  p.tail <- cast c;
  map_i_loop f (succ i) c l

let map_i f i = function
| [] -> []
| x :: l ->
  let c = { head = f i x; tail = [] } in
  map_i_loop f (succ i) c l;
  cast c

(** Extensions of OCaml Stdlib *)

let rec compare cmp l1 l2 =
  if l1 == l2 then 0 else
  match l1,l2 with
      [], [] -> 0
    | _::_, [] -> 1
    | [], _::_ -> -1
    | x1::l1, x2::l2 ->
        (match cmp x1 x2 with
           | 0 -> compare cmp l1 l2
           | c -> c)

let rec equal cmp l1 l2 =
  l1 == l2 ||
  match l1, l2 with
    | [], [] -> true
    | x1 :: l1, x2 :: l2 ->
      cmp x1 x2 && equal cmp l1 l2
    | _ -> false

let is_empty = function
| [] -> true
| _ -> false

let mem_f cmp x l = List.exists (cmp x) l

let intersect cmp l1 l2 =
  filter (fun x -> mem_f cmp x l2) l1

let union cmp l1 l2 =
  let rec urec = function
    | [] -> l2
    | a::l -> if mem_f cmp a l2 then urec l else a::urec l
  in
  urec l1

let subtract cmp l1 l2 =
  if is_empty l2 then l1
  else List.filter (fun x -> not (mem_f cmp x l2)) l1

let unionq l1 l2 = union (==) l1 l2
let subtractq l1 l2 = subtract (==) l1 l2

let interval n m =
  let rec interval_n (l,m) =
    if n > m then l else interval_n (m::l, pred m)
  in
  interval_n ([], m)

let addn n v =
  let rec aux n l =
    if Int.equal n 0 then l
    else aux (pred n) (v :: l)
  in
  if n < 0 then invalid_arg "List.addn"
  else aux n

let make n v = addn n v []

let assign l n e =
  let rec assrec stk l i = match l, i with
    | ((h::t), 0) -> List.rev_append stk (e :: t)
    | ((h::t), n) -> assrec (h :: stk) t (pred n)
    | ([], _) -> failwith "List.assign"
  in
  assrec [] l n

let rec smartmap f l = match l with
    [] -> l
  | h::tl ->
      let h' = f h and tl' = smartmap f tl in
        if h'==h && tl'==tl then l
        else h'::tl'

let map_left = map

let map2_i f i l1 l2 =
  let rec map_i i = function
    | ([], []) -> []
    | ((h1::t1), (h2::t2)) -> let v = f i h1 h2 in v :: map_i (succ i) (t1,t2)
    | (_, _) -> invalid_arg "map2_i"
  in
  map_i i (l1,l2)

let map3 f l1 l2 l3 =
  let rec map = function
    | ([], [], []) -> []
    | ((h1::t1), (h2::t2), (h3::t3)) -> let v = f h1 h2 h3 in v::map (t1,t2,t3)
    | (_, _, _) -> invalid_arg "map3"
  in
  map (l1,l2,l3)

let map4 f l1 l2 l3 l4 =
  let rec map = function
    | ([], [], [], []) -> []
    | ((h1::t1), (h2::t2), (h3::t3), (h4::t4)) -> let v = f h1 h2 h3 h4 in v::map (t1,t2,t3,t4)
    | (_, _, _, _) -> invalid_arg "map4"
  in
  map (l1,l2,l3,l4)

let rec smartfilter f l = match l with
    [] -> l
  | h::tl ->
      let tl' = smartfilter f tl in
        if f h then
          if tl' == tl then l
          else h :: tl'
        else tl'

let rec extend l a l' = match l,l' with
  | true::l, b::l' -> b :: extend l a l'
  | false::l, l' -> a :: extend l a l'
  | [], [] -> []
  | _ -> invalid_arg "extend"

let count f l =
  let rec aux acc = function
    | [] -> acc
    | h :: t -> if f h then aux (acc + 1) t else aux acc t in
  aux 0 l

let rec index_f f x l n = match l with
| [] -> raise Not_found
| y :: l -> if f x y then n else index_f f x l (succ n)

let index f x l = index_f f x l 1

let index0 f x l = index_f f x l 0

let fold_left_until f accu s =
  let rec aux accu = function
    | [] -> accu
    | x :: xs -> match f accu x with CSig.Stop x -> x | CSig.Cont i -> aux i xs in
  aux accu s

let fold_right_i f i l =
  let rec it_f i l a = match l with
    | [] -> a
    | b::l -> f (i-1) b (it_f (i-1) l a)
  in
  it_f (List.length l + i) l

let fold_left_i f =
  let rec it_list_f i a = function
    | [] -> a
    | b::l -> it_list_f (i+1) (f i a b) l
  in
  it_list_f

let rec fold_left3 f accu l1 l2 l3 =
  match (l1, l2, l3) with
    ([], [], []) -> accu
  | (a1::l1, a2::l2, a3::l3) -> fold_left3 f (f accu a1 a2 a3) l1 l2 l3
  | (_, _, _) -> invalid_arg "List.fold_left3"

(* [fold_right_and_left f [a1;...;an] hd =
   f (f (... (f (f hd
                   an
                   [an-1;...;a1])
              an-1
              [an-2;...;a1])
         ...)
        a2
        [a1])
     a1
     []] *)

let fold_right_and_left f l hd =
  let rec aux tl = function
    | [] -> hd
    | a::l -> let hd = aux (a::tl) l in f hd a tl
   in aux [] l

let iteri f l = fold_left_i (fun i _ x -> f i x) 0 () l

let for_all_i p =
  let rec for_all_p i = function
    | [] -> true
    | a::l -> p i a && for_all_p (i+1) l
  in
  for_all_p

let except cmp x l = List.filter (fun y -> not (cmp x y)) l

let remove = except (* Alias *)

let rec remove_first p = function
  | b::l when p b -> l
  | b::l -> b::remove_first p l
  | [] -> raise Not_found

let extract_first p li =
  let rec loop rev_left = function
    | [] -> raise Not_found
    | x::right ->
       if p x then List.rev_append rev_left right, x
       else loop (x :: rev_left) right
  in loop [] li

let insert p v l =
  let rec insrec = function
    | [] -> [v]
    | h::tl -> if p v h then v::h::tl else h::insrec tl
  in
  insrec l

let add_set cmp x l = if mem_f cmp x l then l else x :: l

(** List equality up to permutation (but considering multiple occurrences) *)

let eq_set cmp l1 l2 =
  let rec aux l1 = function
  | [] -> is_empty l1
  | a::l2 -> aux (remove_first (cmp a) l1) l2 in
  try aux l1 l2 with Not_found -> false

let for_all2eq f l1 l2 =
  try List.for_all2 f l1 l2 with Invalid_argument _ -> false

let filteri p =
  let rec filter_i_rec i = function
    | [] -> []
    | x::l -> let l' = filter_i_rec (succ i) l in if p i x then x::l' else l'
  in
  filter_i_rec 0

let partitioni p =
  let rec aux i = function
    | [] -> [], []
    | x :: l ->
        let (l1, l2) = aux (succ i) l in
        if p i x then (x :: l1, l2)
        else (l1, x :: l2)
  in aux 0

let rec sep_last = function
  | [] -> failwith "sep_last"
  | hd::[] -> (hd,[])
  | hd::tl -> let (l,tl) = sep_last tl in (l,hd::tl)

let rec find_map f = function
| [] -> raise Not_found
| x :: l ->
  match f x with
  | None -> find_map f l
  | Some y -> y

(* FIXME: we should avoid relying on the generic hash function,
   just as we'd better avoid Pervasives.compare *)

let uniquize l =
  let visited = Hashtbl.create 23 in
  let rec aux acc changed = function
    | h::t -> if Hashtbl.mem visited h then aux acc true t else
          begin
            Hashtbl.add visited h h;
            aux (h::acc) changed t
          end
    | [] -> if changed then List.rev acc else l
  in aux [] false l

(** [sort_uniquize] might be an alternative to the hashtbl-based
    [uniquize], when the order of the elements is irrelevant *)

let rec uniquize_sorted cmp = function
  | a::b::l when Int.equal (cmp a b) 0 -> uniquize_sorted cmp (a::l)
  | a::l -> a::uniquize_sorted cmp l
  | [] -> []

let sort_uniquize cmp l = uniquize_sorted cmp (List.sort cmp l)

(* FIXME: again, generic hash function *)

let distinct l =
  let visited = Hashtbl.create 23 in
  let rec loop = function
    | h::t ->
        if Hashtbl.mem visited h then false
        else
          begin
            Hashtbl.add visited h h;
            loop t
          end
    | [] -> true
  in loop l

let distinct_f cmp l =
  let rec loop = function
    | a::b::_ when Int.equal (cmp a b) 0 -> false
    | a::l -> loop l
    | [] -> true
  in loop (List.sort cmp l)

let rec merge_uniq cmp l1 l2 =
  match l1, l2 with
  | [], l2 -> l2
  | l1, [] -> l1
  | h1 :: t1, h2 :: t2 ->
      let c = cmp h1 h2 in
      if Int.equal c 0
      then h1 :: merge_uniq cmp t1 t2
      else if c <= 0
      then h1 :: merge_uniq cmp t1 l2
      else h2 :: merge_uniq cmp l1 t2

let rec duplicates cmp = function
  | [] -> []
  | x::l ->
      let l' = duplicates cmp l in
      if mem_f cmp x l then add_set cmp x l' else l'

let rec filter2_loop f p q l1 l2 = match l1, l2 with
| [], [] -> ()
| x :: l1, y :: l2 ->
  if f x y then
    let c1 = { head = x; tail = [] } in
    let c2 = { head = y; tail = [] } in
    let () = p.tail <- cast c1 in
    let () = q.tail <- cast c2 in
    filter2_loop f c1 c2 l1 l2
  else
    filter2_loop f p q l1 l2
| _ -> invalid_arg "List.filter2"

let filter2 f l1 l2 =
  let c1 = { head = Obj.magic 0; tail = [] } in
  let c2 = { head = Obj.magic 0; tail = [] } in
  filter2_loop f c1 c2 l1 l2;
  (c1.tail, c2.tail)

let rec map_filter_loop f p = function
  | [] -> ()
  | x :: l ->
    match f x with
    | None -> map_filter_loop f p l
    | Some y ->
      let c = { head = y; tail = [] } in
      p.tail <- cast c;
      map_filter_loop f c l

let map_filter f l =
  let c = { head = Obj.magic 0; tail = [] } in
  map_filter_loop f c l;
  c.tail

let rec map_filter_i_loop f i p = function
  | [] -> ()
  | x :: l ->
    match f i x with
    | None -> map_filter_i_loop f (succ i) p l
    | Some y ->
      let c = { head = y; tail = [] } in
      p.tail <- cast c;
      map_filter_i_loop f (succ i) c l

let map_filter_i f l =
  let c = { head = Obj.magic 0; tail = [] } in
  map_filter_i_loop f 0 c l;
  c.tail

let rec filter_with filter l = match filter, l with
| [], [] -> []
| true :: filter, x :: l -> x :: filter_with filter l
| false :: filter, _ :: l -> filter_with filter l
| _ -> invalid_arg "List.filter_with"

(* FIXME: again, generic hash function *)

let subset l1 l2 =
  let t2 = Hashtbl.create 151 in
  List.iter (fun x -> Hashtbl.add t2 x ()) l2;
  let rec look = function
    | [] -> true
    | x::ll -> try Hashtbl.find t2 x; look ll with Not_found -> false
  in
  look l1

(** [goto i l] splits [l] into two lists [(l1,l2)] such that
    [(List.rev l1)++l2=l] and [l1] has length [i].  It raises
    [IndexOutOfRange] when [i] is negative or greater than the
    length of [l]. *)
exception IndexOutOfRange
let goto n l =
  let rec goto i acc = function
    | tl when Int.equal i 0 -> (acc, tl)
    | h::t -> goto (pred i) (h::acc) t
    | [] -> raise IndexOutOfRange
  in
  goto n [] l

(* [chop i l] splits [l] into two lists [(l1,l2)] such that
   [l1++l2=l] and [l1] has length [i].
   It raises [Failure] when [i] is negative or greater than the length of [l]  *)

let chop n l =
  try let (h,t) = goto n l in (List.rev h,t)
  with IndexOutOfRange -> failwith "List.chop"
    (* spiwack: should raise [IndexOutOfRange] but I'm afraid of missing
       a try/with when replacing the exception. *)

(* [split_when p l] splits [l] into two lists [(l1,a::l2)] such that
    [l1++(a::l2)=l], [p a=true] and [p b = false] for every element [b] of [l1].
    If there is no such [a], then it returns [(l,[])] instead *)
let split_when p =
  let rec split_when_loop x y =
    match y with
      | []      -> (List.rev x,[])
      | (a::l)  -> if (p a) then (List.rev x,y) else split_when_loop (a::x) l
  in
  split_when_loop []

let rec split3 = function
  | [] -> ([], [], [])
  | (x,y,z)::l ->
      let (rx, ry, rz) = split3 l in (x::rx, y::ry, z::rz)

let firstn n l =
  let rec aux acc n l =
    match n, l with
    | 0, _ -> List.rev acc
    | n, h::t -> aux (h::acc) (pred n) t
    | _ -> failwith "firstn"
  in
  aux [] n l

let rec last = function
  | [] -> failwith "List.last"
  | [x] -> x
  | _ :: l -> last l

let lastn n l =
  let len = List.length l in
  let rec aux m l =
    if Int.equal m n then l else aux (m - 1) (List.tl l)
  in
  if len < n then failwith "lastn" else aux len l

let rec skipn n l = match n,l with
  | 0, _ -> l
  | _, [] -> failwith "List.skipn"
  | n, _::l -> skipn (pred n) l

let skipn_at_least n l =
  try skipn n l with Failure _ -> []

let prefix_of cmp prefl l =
  let rec prefrec = function
    | (h1::t1, h2::t2) -> cmp h1 h2 && prefrec (t1,t2)
    | ([], _) -> true
    | _ -> false
  in
  prefrec (prefl,l)

(** if [l=p++t] then [drop_prefix p l] is [t] else [l] *)

let drop_prefix cmp p l =
  let rec drop_prefix_rec = function
    | (h1::tp, h2::tl) when cmp h1 h2 -> drop_prefix_rec (tp,tl)
    | ([], tl) -> tl
    | _ -> l
  in
  drop_prefix_rec (p,l)

let map_append f l = List.flatten (List.map f l)

let map_append2 f l1 l2 = List.flatten (List.map2 f l1 l2)

let share_tails l1 l2 =
  let rec shr_rev acc = function
    | ((x1::l1), (x2::l2)) when x1 == x2 -> shr_rev (x1::acc) (l1,l2)
    | (l1,l2) -> (List.rev l1, List.rev l2, acc)
  in
  shr_rev [] (List.rev l1, List.rev l2)

let rec fold_map f e = function
  |  []  -> (e,[])
  |  h::t ->
       let e',h' = f e h in
       let e'',t' = fold_map f e' t in
         e'',h'::t'

(* (* tail-recursive version of the above function *)
let fold_map f e l =
  let g (e,b') h =
    let (e',h') = f e h in
      (e',h'::b')
  in
  let (e',lrev) = List.fold_left g (e,[]) l in
    (e',List.rev lrev)
*)

(* The same, based on fold_right, with the effect accumulated on the right *)
let fold_map' f l e =
  List.fold_right (fun x (l,e) -> let (y,e) = f x e in (y::l,e)) l ([],e)

let map_assoc f = List.map (fun (x,a) -> (x,f a))

let rec assoc_f f a = function
  | (x, e) :: xs -> if f a x then e else assoc_f f a xs
  | [] -> raise Not_found

let remove_assoc_f f a l =
  try remove_first (fun (x,_) -> f a x) l with Not_found -> l

let mem_assoc_f f a l = List.exists (fun (x,_) -> f a x) l

(* A generic cartesian product: for any operator (**),
   [cartesian (**) [x1;x2] [y1;y2] = [x1**y1; x1**y2; x2**y1; x2**y1]],
   and so on if there are more elements in the lists. *)

let cartesian op l1 l2 =
  map_append (fun x -> List.map (op x) l2) l1

(* [cartesians] is an n-ary cartesian product: it iterates
   [cartesian] over a list of lists.  *)

let cartesians op init ll =
  List.fold_right (cartesian op) ll [init]

(* combinations [[a;b];[c;d]] gives [[a;c];[a;d];[b;c];[b;d]] *)

let combinations l = cartesians (fun x l -> x::l) [] l

let rec combine3 x y z = 
  match x, y, z with
  | [], [], [] -> []
  | (x :: xs), (y :: ys), (z :: zs) ->
      (x, y, z) :: combine3 xs ys zs
  | _, _, _ -> invalid_arg "List.combine3"
  
(* Keep only those products that do not return None *)

let cartesian_filter op l1 l2 =
  map_append (fun x -> map_filter (op x) l2) l1

(* Keep only those products that do not return None *)

let cartesians_filter op init ll =
  List.fold_right (cartesian_filter op) ll [init]

(* Drop the last element of a list *)

let rec drop_last = function
  | [] -> assert false
  | hd :: [] -> []
  | hd :: tl -> hd :: drop_last tl

(* Factorize lists of pairs according to the left argument *)
let rec factorize_left cmp = function
  | (a,b)::l ->
      let al,l' = partition (fun (a',_) -> cmp a a') l in
      (a,(b::List.map snd al)) :: factorize_left cmp l'
  | [] -> []

module type MonoS = sig
  type elt
  val equal : elt list -> elt list -> bool
  val mem : elt -> elt list -> bool
  val assoc : elt -> (elt * 'a) list -> 'a
  val mem_assoc : elt -> (elt * 'a) list -> bool
  val remove_assoc : elt -> (elt * 'a) list -> (elt * 'a) list
  val mem_assoc_sym : elt -> ('a * elt) list -> bool
end
end

module CArray : sig

(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

module type S = module type of Array

module type ExtS =
sig
  include S
  val compare : ('a -> 'a -> int) -> 'a array -> 'a array -> int
  (** First size comparison, then lexicographic order. *)

  val equal : ('a -> 'a -> bool) -> 'a array -> 'a array -> bool
  (** Lift equality to array type. *)

  val equal_norefl : ('a -> 'a -> bool) -> 'a array -> 'a array -> bool
  (** Like {!equal} but does not assume that equality is reflexive: no
      optimisation is performed if both arrays are physically the
      same. *)

  val is_empty : 'a array -> bool
  (** True whenever the array is empty. *)

  val exists : ('a -> bool) -> 'a array -> bool
  (** As [List.exists] but on arrays. *)

  val exists2 : ('a -> 'b -> bool) -> 'a array -> 'b array -> bool

  val for_all : ('a -> bool) -> 'a array -> bool
  val for_all2 : ('a -> 'b -> bool) -> 'a array -> 'b array -> bool
  val for_all3 : ('a -> 'b -> 'c -> bool) ->
    'a array -> 'b array -> 'c array -> bool
  val for_all4 : ('a -> 'b -> 'c -> 'd -> bool) ->
    'a array -> 'b array -> 'c array -> 'd array -> bool
  val for_all_i : (int -> 'a -> bool) -> int -> 'a array -> bool

  val findi : (int -> 'a -> bool) -> 'a array -> int option

  val hd : 'a array -> 'a
  (** First element of an array, or [Failure "Array.hd"] if empty. *)

  val tl : 'a array -> 'a array
  (** Remaining part of [hd], or [Failure "Array.tl"] if empty. *)

  val last : 'a array -> 'a
  (** Last element of an array, or [Failure "Array.last"] if empty. *)

  val cons : 'a -> 'a array -> 'a array
  (** Append an element on the left. *)

  val rev : 'a array -> unit
  (** In place reversal. *)

  val fold_right_i :
    (int -> 'b -> 'a -> 'a) -> 'b array -> 'a -> 'a
  val fold_left_i : (int -> 'a -> 'b -> 'a) -> 'a -> 'b array -> 'a
  val fold_right2 :
    ('a -> 'b -> 'c -> 'c) -> 'a array -> 'b array -> 'c -> 'c
  val fold_left2 :
    ('a -> 'b -> 'c -> 'a) -> 'a -> 'b array -> 'c array -> 'a
  val fold_left3 :
    ('a -> 'b -> 'c -> 'd -> 'a) -> 'a -> 'b array -> 'c array -> 'd array -> 'a
  val fold_left2_i :
    (int -> 'a -> 'b -> 'c -> 'a) -> 'a -> 'b array -> 'c array -> 'a
  val fold_left_from : int -> ('a -> 'b -> 'a) -> 'a -> 'b array -> 'a

  val map_to_list : ('a -> 'b) -> 'a array -> 'b list
  (** Composition of [map] and [to_list]. *)

  val map_of_list : ('a -> 'b) -> 'a list -> 'b array
  (** Composition of [map] and [of_list]. *)

  val chop : int -> 'a array -> 'a array * 'a array
  (** [chop i a] returns [(a1, a2)] s.t. [a = a1 + a2] and [length a1 = n].
      Raise [Failure "Array.chop"] if [i] is not a valid index. *)

  val smartmap : ('a -> 'a) -> 'a array -> 'a array
  (** [smartmap f a] behaves as [map f a] but returns [a] instead of a copy when
      [f x == x] for all [x] in [a]. *)

  val smartfoldmap : ('r -> 'a -> 'r * 'a) -> 'r -> 'a array -> 'r * 'a array
  (** Same as [smartmap] but threads an additional state left-to-right. *)

  val map2 : ('a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array
  val map2_i : (int -> 'a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array
  val map3 :
    ('a -> 'b -> 'c -> 'd) -> 'a array -> 'b array -> 'c array -> 'd array

  val map_left : ('a -> 'b) -> 'a array -> 'b array
  (** As [map] but guaranteed to be left-to-right. *)

  val iter2 : ('a -> 'b -> unit) -> 'a array -> 'b array -> unit
  (** Iter on two arrays. Raise [Invalid_argument "Array.iter2"] if sizes differ. *)

  val fold_map' : ('a -> 'c -> 'b * 'c) -> 'a array -> 'c -> 'b array * 'c
  val fold_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b array -> 'a * 'c array
  val fold_map2' :
    ('a -> 'b -> 'c -> 'd * 'c) -> 'a array -> 'b array -> 'c -> 'd array * 'c

  val distinct : 'a array -> bool
  (** Return [true] if every element of the array is unique (for default 
      equality). *)

  val rev_of_list : 'a list -> 'a array
  (** [rev_of_list l] is equivalent to [Array.of_list (List.rev l)]. *)

  val rev_to_list : 'a array -> 'a list
  (** [rev_to_list a] is equivalent to [List.rev (List.of_array a)]. *)

  val filter_with : bool list -> 'a array -> 'a array
  (** [filter_with b a] selects elements of [a] whose corresponding element in
      [b] is [true].  Raise [Invalid_argument _] when sizes differ. *)

end

include ExtS

module Fun1 :
sig
  val map : ('r -> 'a -> 'b) -> 'r -> 'a array -> 'b array
  (** [Fun1.map f x v = map (f x) v] *)

  val smartmap : ('r -> 'a -> 'a) -> 'r -> 'a array -> 'a array
  (** [Fun1.smartmap f x v = smartmap (f x) v] *)

  val iter : ('r -> 'a -> unit) -> 'r -> 'a array -> unit
  (** [Fun1.iter f x v = iter (f x) v] *)

end
(** The functions defined in this module are the same as the main ones, except
    that they are all higher-order, and their function arguments have an
    additional parameter. This allows us to prevent closure creation in critical
    cases. *)
end = struct

(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

module type S = module type of Array

module type ExtS =
sig
  include S
  val compare : ('a -> 'a -> int) -> 'a array -> 'a array -> int
  val equal : ('a -> 'a -> bool) -> 'a array -> 'a array -> bool
  val equal_norefl : ('a -> 'a -> bool) -> 'a array -> 'a array -> bool
  val is_empty : 'a array -> bool
  val exists : ('a -> bool) -> 'a array -> bool
  val exists2 : ('a -> 'b -> bool) -> 'a array -> 'b array -> bool
  val for_all : ('a -> bool) -> 'a array -> bool
  val for_all2 : ('a -> 'b -> bool) -> 'a array -> 'b array -> bool
  val for_all3 : ('a -> 'b -> 'c -> bool) ->
    'a array -> 'b array -> 'c array -> bool
  val for_all4 : ('a -> 'b -> 'c -> 'd -> bool) ->
    'a array -> 'b array -> 'c array -> 'd array -> bool
  val for_all_i : (int -> 'a -> bool) -> int -> 'a array -> bool
  val findi : (int -> 'a -> bool) -> 'a array -> int option
  val hd : 'a array -> 'a
  val tl : 'a array -> 'a array
  val last : 'a array -> 'a
  val cons : 'a -> 'a array -> 'a array
  val rev : 'a array -> unit
  val fold_right_i :
    (int -> 'b -> 'a -> 'a) -> 'b array -> 'a -> 'a
  val fold_left_i : (int -> 'a -> 'b -> 'a) -> 'a -> 'b array -> 'a
  val fold_right2 :
    ('a -> 'b -> 'c -> 'c) -> 'a array -> 'b array -> 'c -> 'c
  val fold_left2 :
    ('a -> 'b -> 'c -> 'a) -> 'a -> 'b array -> 'c array -> 'a
  val fold_left3 :
    ('a -> 'b -> 'c -> 'd -> 'a) -> 'a -> 'b array -> 'c array -> 'd array -> 'a
  val fold_left2_i :
    (int -> 'a -> 'b -> 'c -> 'a) -> 'a -> 'b array -> 'c array -> 'a
  val fold_left_from : int -> ('a -> 'b -> 'a) -> 'a -> 'b array -> 'a
  val map_to_list : ('a -> 'b) -> 'a array -> 'b list
  val map_of_list : ('a -> 'b) -> 'a list -> 'b array
  val chop : int -> 'a array -> 'a array * 'a array
  val smartmap : ('a -> 'a) -> 'a array -> 'a array
  val smartfoldmap : ('r -> 'a -> 'r * 'a) -> 'r -> 'a array -> 'r * 'a array
  val map2 : ('a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array
  val map2_i : (int -> 'a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array
  val map3 :
    ('a -> 'b -> 'c -> 'd) -> 'a array -> 'b array -> 'c array -> 'd array
  val map_left : ('a -> 'b) -> 'a array -> 'b array
  val iter2 : ('a -> 'b -> unit) -> 'a array -> 'b array -> unit
  val fold_map' : ('a -> 'c -> 'b * 'c) -> 'a array -> 'c -> 'b array * 'c
  val fold_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b array -> 'a * 'c array
  val fold_map2' :
    ('a -> 'b -> 'c -> 'd * 'c) -> 'a array -> 'b array -> 'c -> 'd array * 'c
  val distinct : 'a array -> bool
  val rev_of_list : 'a list -> 'a array
  val rev_to_list : 'a array -> 'a list
  val filter_with : bool list -> 'a array -> 'a array
end

include Array

let uget = Array.unsafe_get

(* Arrays *)

let compare cmp v1 v2 =
  if v1 == v2 then 0
  else
    let len = Array.length v1 in
    let c = Int.compare len (Array.length v2) in
    if c <> 0 then c else
      let rec loop i =
        if i < 0 then 0
        else
          let x = uget v1 i in
          let y = uget v2 i in
          let c = cmp x y in
          if c <> 0 then c
          else loop (i - 1)
      in
      loop (len - 1)

let equal_norefl cmp t1 t2 =
  let len = Array.length t1 in
  if not (Int.equal len (Array.length t2)) then false
  else
    let rec aux i =
      if i < 0 then true
      else
        let x = uget t1 i in
        let y = uget t2 i in
        cmp x y && aux (pred i)
    in
    aux (len - 1)

let equal cmp t1 t2 =
  if t1 == t2 then true else equal_norefl cmp t1 t2
    

let is_empty array = Int.equal (Array.length array) 0

let exists f v =
  let rec exrec = function
    | -1 -> false
    | n -> f (uget v n) || (exrec (n-1))
  in
  exrec ((Array.length v)-1)

let exists2 f v1 v2 =
  let rec exrec = function
    | -1 -> false
    | n -> f (uget v1 n) (uget v2 n) || (exrec (n-1))
  in
  let lv1 = Array.length v1 in
  lv1 = Array.length v2 && exrec (lv1-1)

let for_all f v =
  let rec allrec = function
    | -1 -> true
    | n ->
      let ans = f (uget v n) in
      ans && (allrec (n-1))
  in
  allrec ((Array.length v)-1)

let for_all2 f v1 v2 =
  let rec allrec = function
    | -1 -> true
    | n ->
      let ans = f (uget v1 n) (uget v2 n) in
      ans && (allrec (n-1))
  in
  let lv1 = Array.length v1 in
  lv1 = Array.length v2 && allrec (pred lv1)

let for_all3 f v1 v2 v3 =
  let rec allrec = function
    | -1 -> true
    | n ->
      let ans = f (uget v1 n)
        (uget v2 n) (uget v3 n)
      in
      ans && (allrec (n-1))
  in
  let lv1 = Array.length v1 in
  lv1 = Array.length v2 && lv1 = Array.length v3 && allrec (pred lv1)

let for_all4 f v1 v2 v3 v4 =
  let rec allrec = function
    | -1 -> true
    | n ->
      let ans = f (uget v1 n)
        (uget v2 n) (uget v3 n) (uget v4 n)
      in
      ans && (allrec (n-1))
  in
  let lv1 = Array.length v1 in
  lv1 = Array.length v2 &&
  lv1 = Array.length v3 &&
  lv1 = Array.length v4 &&
  allrec (pred lv1)

let for_all_i f i v =
  let len = Array.length v in
  let rec allrec i n =
    n = len || f i (uget v n) && allrec (i+1) (n+1) in
  allrec i 0

exception Found of int

let findi (pred: int -> 'a -> bool) (arr: 'a array) : int option =
  try
    for i=0 to Array.length arr - 1 do
      if pred i (uget arr i) then raise (Found i) done;
    None
  with Found i -> Some i

let hd v =
  match Array.length v with
    | 0 -> failwith "Array.hd"
    | _ -> uget v 0

let tl v =
  match Array.length v with
    | 0 -> failwith "Array.tl"
    | n -> Array.sub v 1 (pred n)

let last v =
  match Array.length v with
    | 0 -> failwith "Array.last"
    | n -> uget v (pred n)

let cons e v =
  let len = Array.length v in
  let ans = Array.make (Array.length v + 1) e in
  let () = Array.blit v 0 ans 1 len in
  ans

let rev t =
  let n=Array.length t in
    if n <=0 then ()
    else
      for i = 0 to pred (n/2) do
        let tmp = uget t ((pred n)-i) in
        Array.unsafe_set t ((pred n)-i) (uget t i);
        Array.unsafe_set t i tmp
      done

let fold_right_i f v a =
  let rec fold a n =
    if n=0 then a
    else
      let k = n-1 in
      fold (f k (uget v k) a) k in
  fold a (Array.length v)

let fold_left_i f v a =
  let n = Array.length a in
  let rec fold i v = if i = n then v else fold (succ i) (f i v (uget a i)) in
  fold 0 v

let fold_right2 f v1 v2 a =
  let lv1 = Array.length v1 in
  let rec fold a n =
    if n=0 then a
    else
      let k = n-1 in
      fold (f (uget v1 k) (uget v2 k) a) k in
  if Array.length v2 <> lv1 then invalid_arg "Array.fold_right2";
  fold a lv1

let fold_left2 f a v1 v2 =
  let lv1 = Array.length v1 in
  let rec fold a n =
    if n >= lv1 then a else fold (f a (uget v1 n) (uget v2 n)) (succ n)
  in
  if Array.length v2 <> lv1 then invalid_arg "Array.fold_left2";
  fold a 0

let fold_left2_i f a v1 v2 =
  let lv1 = Array.length v1 in
  let rec fold a n =
    if n >= lv1 then a else fold (f n a (uget v1 n) (uget v2 n)) (succ n)
  in
  if Array.length v2 <> lv1 then invalid_arg "Array.fold_left2";
  fold a 0

let fold_left3 f a v1 v2 v3 =
  let lv1 = Array.length v1 in
  let rec fold a n =
    if n >= lv1 then a
    else fold (f a (uget v1 n) (uget v2 n) (uget v3 n)) (succ n)
  in
  if Array.length v2 <> lv1 || Array.length v3 <> lv1 then
    invalid_arg "Array.fold_left2";
  fold a 0

let fold_left_from n f a v =
  let len = Array.length v in
  let () = if n < 0 then invalid_arg "Array.fold_left_from" in
  let rec fold a n =
    if n >= len then a else fold (f a (uget v n)) (succ n)
  in
  fold a n

let rev_of_list = function
| [] -> [| |]
| x :: l ->
  let len = List.length l in
  let ans = Array.make (succ len) x in
  let rec set i = function
  | [] -> ()
  | x :: l ->
    Array.unsafe_set ans i x;
    set (pred i) l
  in
  let () = set (len - 1) l in
  ans

let map_to_list f v =
  List.map f (Array.to_list v)

let map_of_list f l =
  let len = List.length l in
  let rec fill i v = function
  | [] -> ()
  | x :: l ->
    Array.unsafe_set v i (f x);
    fill (succ i) v l
  in
  match l with
  | [] -> [||]
  | x :: l ->
    let ans = Array.make len (f x) in
    let () = fill 1 ans l in
    ans

let chop n v =
  let vlen = Array.length v in
  if n > vlen then failwith "Array.chop";
  (Array.sub v 0 n, Array.sub v n (vlen-n))

(* If none of the elements is changed by f we return ar itself.
   The while loop looks for the first such an element.
   If found, we break here and the new array is produced,
   but f is not re-applied to elements that are already checked *)
let smartmap f (ar : 'a array) =
  let len = Array.length ar in
  let i = ref 0 in
  let break = ref true in
  let temp = ref None in
  while !break && (!i < len) do
    let v = Array.unsafe_get ar !i in
    let v' = f v in
    if v == v' then incr i
    else begin
      break := false;
      temp := Some v';
    end
  done;
  if !i < len then begin
    (** The array is not the same as the original one *)
    let ans : 'a array = Array.copy ar in
    let v = match !temp with None -> assert false | Some x -> x in
    Array.unsafe_set ans !i v;
    incr i;
    while !i < len do
      let v = Array.unsafe_get ar !i in
      let v' = f v in
      if v != v' then Array.unsafe_set ans !i v';
      incr i
    done;
    ans
  end else ar

(** Same as [smartmap] but threads a state meanwhile *)
let smartfoldmap f accu (ar : 'a array) =
  let len = Array.length ar in
  let i = ref 0 in
  let break = ref true in
  let r = ref accu in
  (** This variable is never accessed unset *)
  let temp = ref None in
  while !break && (!i < len) do
    let v = Array.unsafe_get ar !i in
    let (accu, v') = f !r v in
    r := accu;
    if v == v' then incr i
    else begin
      break := false;
      temp := Some v';
    end
  done;
  if !i < len then begin
    let ans : 'a array = Array.copy ar in
    let v = match !temp with None -> assert false | Some x -> x in
    Array.unsafe_set ans !i v;
    incr i;
    while !i < len do
      let v = Array.unsafe_get ar !i in
      let (accu, v') = f !r v in
      r := accu;
      if v != v' then Array.unsafe_set ans !i v';
      incr i
    done;
    !r, ans
  end else !r, ar

let map2 f v1 v2 =
  let len1 = Array.length v1 in
  let len2 = Array.length v2 in
  let () = if not (Int.equal len1 len2) then invalid_arg "Array.map2" in
  if Int.equal len1 0 then
    [| |]
  else begin
    let res = Array.make len1 (f (uget v1 0) (uget v2 0)) in
    for i = 1 to pred len1 do
      Array.unsafe_set res i (f (uget v1 i) (uget v2 i))
    done;
    res
  end

let map2_i f v1 v2 =
  let len1 = Array.length v1 in
  let len2 = Array.length v2 in
  let () = if not (Int.equal len1 len2) then invalid_arg "Array.map2" in
  if Int.equal len1 0 then
    [| |]
  else begin
    let res = Array.make len1 (f 0 (uget v1 0) (uget v2 0)) in
    for i = 1 to pred len1 do
      Array.unsafe_set res i (f i (uget v1 i) (uget v2 i))
    done;
    res
  end

let map3 f v1 v2 v3 =
  let len1 = Array.length v1 in
  let () =
    if len1 <> Array.length v2 || len1 <> Array.length v3
    then invalid_arg "Array.map3"
  in
  if Int.equal len1 0 then
    [| |]
  else begin
    let res = Array.make len1 (f (uget v1 0) (uget v2 0) (uget v3 0)) in
    for i = 1 to pred len1 do
      Array.unsafe_set res i (f (uget v1 i) (uget v2 i) (uget v3 i))
    done;
    res
  end

let map_left f a = (* Ocaml does not guarantee Array.map is LR *)
  let l = Array.length a in (* (even if so), then we rewrite it *)
  if Int.equal l 0 then [||] else begin
    let r = Array.make l (f (uget a 0)) in
    for i = 1 to l - 1 do
      Array.unsafe_set r i (f (uget a i))
    done;
    r
  end

let iter2 f v1 v2 =
  let len1 = Array.length v1 in
  let len2 = Array.length v2 in
  let () = if not (Int.equal len2 len1) then invalid_arg "Array.iter2" in
  for i = 0 to len1 - 1 do f (uget v1 i) (uget v2 i) done

let pure_functional = false

let fold_map' f v e =
if pure_functional then
  let (l,e) =
    Array.fold_right
      (fun x (l,e) -> let (y,e) = f x e in (y::l,e))
      v ([],e) in
  (Array.of_list l,e)
else
  let e' = ref e in
  let v' = Array.map (fun x -> let (y,e) = f x !e' in e' := e; y) v in
  (v',!e')

let fold_map f e v =
  let e' = ref e in
  let v' = Array.map (fun x -> let (e,y) = f !e' x in e' := e; y) v in
  (!e',v')

let fold_map2' f v1 v2 e =
  let e' = ref e in
  let v' =
    map2 (fun x1 x2 -> let (y,e) = f x1 x2 !e' in e' := e; y) v1 v2
  in
  (v',!e')


let distinct v =
  let visited = Hashtbl.create 23 in
  try
    Array.iter
      (fun x ->
        if Hashtbl.mem visited x then raise Exit
        else Hashtbl.add visited x x)
      v;
    true
  with Exit -> false

let rev_to_list a =
  let rec tolist i res =
    if i >= Array.length a then res else tolist (i+1) (uget a i :: res) in
  tolist 0 []

let filter_with filter v =
  Array.of_list (CList.filter_with filter (Array.to_list v))

module Fun1 =
struct

  let map f arg v = match v with
  | [| |] -> [| |]
  | _ ->
    let len = Array.length v in
    let x0 = Array.unsafe_get v 0 in
    let ans = Array.make len (f arg x0) in
    for i = 1 to pred len do
      let x = Array.unsafe_get v i in
      Array.unsafe_set ans i (f arg x)
    done;
    ans

  let smartmap f arg (ar : 'a array) =
    let len = Array.length ar in
    let i = ref 0 in
    let break = ref true in
    let temp = ref None in
    while !break && (!i < len) do
      let v = Array.unsafe_get ar !i in
      let v' = f arg v in
      if v == v' then incr i
      else begin
        break := false;
        temp := Some v';
      end
    done;
    if !i < len then begin
      (** The array is not the same as the original one *)
      let ans : 'a array = Array.copy ar in
      let v = match !temp with None -> assert false | Some x -> x in
      Array.unsafe_set ans !i v;
      incr i;
      while !i < len do
        let v = Array.unsafe_get ar !i in
        let v' = f arg v in
        if v != v' then Array.unsafe_set ans !i v';
        incr i
      done;
      ans
    end else ar

  let iter f arg v =
    let len = Array.length v in
    for i = 0 to pred len do
      let x = uget v i in
      f arg x
    done

end
end



module Hashset : sig
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Adapted from Damien Doligez, projet Para, INRIA Rocquencourt,
    OCaml stdlib. *)

(** The following functor is a specialized version of [Weak.Make].
    Here, the responsibility of computing the hash function is now
    given to the caller, which makes possible the interleaving of the
    hash key computation and the hash-consing. *)

module type EqType = sig
  type t
  val eq : t -> t -> bool
end

type statistics = {
  num_bindings: int;
  num_buckets: int;
  max_bucket_length: int;
  bucket_histogram: int array
}

module type S = sig
  type elt
  (** Type of hashsets elements. *)
  type t
  (** Type of hashsets. *)
  val create : int -> t
  (** [create n] creates a fresh hashset with initial size [n]. *)
  val clear : t -> unit
  (** Clear the contents of a hashset. *)
  val repr : int -> elt -> t -> elt
  (** [repr key constr set] uses [key] to look for [constr]
      in the hashet [set]. If [constr] is in [set], returns the
      specific representation that is stored in [set]. Otherwise,
      [constr] is stored in [set] and will be used as the canonical
      representation of this value in the future. *)
  val stats : t -> statistics
  (** Recover statistics on the table. *)
end

module Make (E : EqType) : S with type elt = E.t

module Combine : sig
  val combine : int -> int -> int
  val combinesmall : int -> int -> int
  val combine3 : int -> int -> int -> int
  val combine4 : int -> int -> int -> int -> int
  val combine5 : int -> int -> int -> int -> int -> int
end

end = struct 

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Adapted from Damien Doligez, projet Para, INRIA Rocquencourt,
    OCaml stdlib. *)

(** The following functor is a specialized version of [Weak.Make].
    Here, the responsibility of computing the hash function is now
    given to the caller, which makes possible the interleaving of the
    hash key computation and the hash-consing. *)

module type EqType = sig
  type t
  val eq : t -> t -> bool
end

type statistics = {
  num_bindings: int;
  num_buckets: int;
  max_bucket_length: int;
  bucket_histogram: int array
}

module type S = sig
  type elt
  type t
  val create : int -> t
  val clear : t -> unit
  val repr : int -> elt -> t -> elt
  val stats : t -> statistics
end

module Make (E : EqType) =
  struct

  type elt = E.t

  let emptybucket = Weak.create 0

  type t = {
    mutable table : elt Weak.t array;
    mutable hashes : int array array;
    mutable limit : int;               (* bucket size limit *)
    mutable oversize : int;            (* number of oversize buckets *)
    mutable rover : int;               (* for internal bookkeeping *)
  }

  let get_index t h = (h land max_int) mod (Array.length t.table)

  let limit = 7
  let over_limit = 2

  let create sz =
    let sz = if sz < 7 then 7 else sz in
    let sz = if sz > Sys.max_array_length then Sys.max_array_length else sz in
    {
      table = Array.make sz emptybucket;
      hashes = Array.make sz [| |];
      limit = limit;
      oversize = 0;
      rover = 0;
    }

  let clear t =
    for i = 0 to Array.length t.table - 1 do
      t.table.(i) <- emptybucket;
      t.hashes.(i) <- [| |];
    done;
    t.limit <- limit;
    t.oversize <- 0

  let iter_weak f t =
    let rec iter_bucket i j b =
      if i >= Weak.length b then () else
      match Weak.check b i with
      | true -> f b t.hashes.(j) i; iter_bucket (i+1) j b
      | false -> iter_bucket (i+1) j b
    in
    for i = 0 to pred (Array.length t.table) do
      iter_bucket 0 i (Array.unsafe_get t.table i)
    done

  let rec count_bucket i b accu =
    if i >= Weak.length b then accu else
    count_bucket (i+1) b (accu + (if Weak.check b i then 1 else 0))

  let min x y = if x - y < 0 then x else y

  let next_sz n = min (3 * n / 2 + 3) Sys.max_array_length
  let prev_sz n = ((n - 3) * 2 + 2) / 3

  let test_shrink_bucket t =
    let bucket = t.table.(t.rover) in
    let hbucket = t.hashes.(t.rover) in
    let len = Weak.length bucket in
    let prev_len = prev_sz len in
    let live = count_bucket 0 bucket 0 in
    if live <= prev_len then begin
      let rec loop i j =
        if j >= prev_len then begin
          if Weak.check bucket i then loop (i + 1) j
          else if Weak.check bucket j then begin
            Weak.blit bucket j bucket i 1;
            hbucket.(i) <- hbucket.(j);
            loop (i + 1) (j - 1);
          end else loop i (j - 1);
        end;
      in
      loop 0 (Weak.length bucket - 1);
      if prev_len = 0 then begin
        t.table.(t.rover) <- emptybucket;
        t.hashes.(t.rover) <- [| |];
      end else begin
        Obj.truncate (Obj.repr bucket) (prev_len + 1);
        Obj.truncate (Obj.repr hbucket) prev_len;
      end;
      if len > t.limit && prev_len <= t.limit then t.oversize <- t.oversize - 1;
    end;
    t.rover <- (t.rover + 1) mod (Array.length t.table)

  let rec resize t =
    let oldlen = Array.length t.table in
    let newlen = next_sz oldlen in
    if newlen > oldlen then begin
      let newt = create newlen in
      let add_weak ob oh oi =
        let setter nb ni _ = Weak.blit ob oi nb ni 1 in
        let h = oh.(oi) in
        add_aux newt setter None h (get_index newt h);
      in
      iter_weak add_weak t;
      t.table <- newt.table;
      t.hashes <- newt.hashes;
      t.limit <- newt.limit;
      t.oversize <- newt.oversize;
      t.rover <- t.rover mod Array.length newt.table;
    end else begin
      t.limit <- max_int;             (* maximum size already reached *)
      t.oversize <- 0;
    end

  and add_aux t setter d h index =
    let bucket = t.table.(index) in
    let hashes = t.hashes.(index) in
    let sz = Weak.length bucket in
    let rec loop i =
      if i >= sz then begin
        let newsz = min (3 * sz / 2 + 3) (Sys.max_array_length - 1) in
        if newsz <= sz then failwith "Weak.Make: hash bucket cannot grow more";
        let newbucket = Weak.create newsz in
        let newhashes = Array.make newsz 0 in
        Weak.blit bucket 0 newbucket 0 sz;
        Array.blit hashes 0 newhashes 0 sz;
        setter newbucket sz d;
        newhashes.(sz) <- h;
        t.table.(index) <- newbucket;
        t.hashes.(index) <- newhashes;
        if sz <= t.limit && newsz > t.limit then begin
          t.oversize <- t.oversize + 1;
          for _i = 0 to over_limit do test_shrink_bucket t done;
        end;
        if t.oversize > Array.length t.table / over_limit then resize t
      end else if Weak.check bucket i then begin
        loop (i + 1)
      end else begin
        setter bucket i d;
        hashes.(i) <- h
      end
    in
    loop 0

  let find_or h t d ifnotfound =
    let index = get_index t h in
    let bucket = t.table.(index) in
    let hashes = t.hashes.(index) in
    let sz = Weak.length bucket in
    let rec loop i =
      if i >= sz then ifnotfound index
      else if h = hashes.(i) then begin
        match Weak.get bucket i with
        | Some v when E.eq v d -> v
        | _ -> loop (i + 1)
      end else loop (i + 1)
    in
    loop 0

  let repr h d t =
    let ifnotfound index = add_aux t Weak.set (Some d) h index; d in
    find_or h t d ifnotfound

  let stats t =
    let fold accu bucket = max (count_bucket 0 bucket 0) accu in
    let max_length = Array.fold_left fold 0 t.table in
    let histogram = Array.make (max_length + 1) 0 in
    let iter bucket =
      let len = count_bucket 0 bucket 0 in
      histogram.(len) <- succ histogram.(len)
    in
    let () = Array.iter iter t.table in
    let fold (num, len, i) k = (num + k * i, len + k, succ i) in
    let (num, len, _) = Array.fold_left fold (0, 0, 0) histogram in
    {
      num_bindings = num;
      num_buckets = len;
      max_bucket_length = Array.length histogram;
      bucket_histogram = histogram;
    }

end

module Combine = struct
    (* These are helper functions to combine the hash keys in a similar
       way as [Hashtbl.hash] does. The constants [alpha] and [beta] must
       be prime numbers. There were chosen empirically. Notice that the
       problem of hashing trees is hard and there are plenty of study on
       this topic. Therefore, there must be room for improvement here. *)
    let alpha = 65599
    let beta  = 7
    let combine x y     = x * alpha + y
    let combine3 x y z   = combine x (combine y z)
    let combine4 x y z t = combine x (combine3 y z t)
    let combine5 x y z t u = combine x (combine4 y z t u)
    let combinesmall x y = beta * x + y
end
end


module Hashcons : sig
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Generic hash-consing. *)

(** {6 Hashconsing functorial interface} *)

module type HashconsedType =
  sig
    (** {6 Generic hashconsing signature}

        Given an equivalence relation [eq], a hashconsing function is a
        function that associates the same canonical element to two elements
        related by [eq]. Usually, the element chosen is canonical w.r.t.
        physical equality [(==)], so as to reduce memory consumption and
        enhance efficiency of equality tests.

        In order to ensure canonicality, we need a way to remember the element
        associated to a class of equivalence; this is done using the table type
        generated by the [Make] functor.
    *)

    type t
    (** Type of objects to hashcons. *)
    type u
    (** Type of hashcons functions for the sub-structures contained in [t].
        Usually a tuple of functions. *)
    val hashcons :  u -> t -> t
    (** The actual hashconsing function, using its fist argument to recursively
        hashcons substructures. It should be compatible with [eq], that is
        [eq x (hashcons f x) = true]. *)
    val eq : t -> t -> bool
    (** A comparison function. It is allowed to use physical equality
        on the sub-terms hashconsed by the [hashcons] function, but it should be
        insensible to shallow copy of the compared object. *)
    val hash : t -> int
    (** A hash function passed to the underlying hashtable structure. [hash]
        should be compatible with [eq], i.e. if [eq x y = true] then
        [hash x = hash y]. *)
  end

module type S =
  sig
    type t
    (** Type of objects to hashcons. *)
    type u
    (** Type of hashcons functions for the sub-structures contained in [t]. *)
    type table
    (** Type of hashconsing tables *)
    val generate : u -> table
    (** This create a hashtable of the hashconsed objects. *)
    val hcons : table -> t -> t
    (** Perform the hashconsing of the given object within the table. *)
    val stats : table -> Hashset.statistics
    (** Recover statistics of the hashconsing table. *)
  end

module Make (X : HashconsedType) : (S with type t = X.t and type u = X.u)
(** Create a new hashconsing, given canonicalization functions. *)

(** {6 Wrappers} *)

(** These are intended to be used together with instances of the [Make]
    functor. *)

val simple_hcons : ('u -> 'tab) -> ('tab -> 't -> 't) -> 'u -> 't -> 't
(** [simple_hcons f sub obj] creates a new table each time it is applied to any
    sub-hash function [sub]. *)

val recursive_hcons : (('t -> 't) * 'u -> 'tab) -> ('tab -> 't -> 't) -> ('u -> 't -> 't)
(** As [simple_hcons] but intended to be used with well-founded data structures. *)

(** {6 Hashconsing of usual structures} *)

module type HashedType = sig type t val hash : t -> int end

module Hstring : (S with type t = string and type u = unit)
(** Hashconsing of strings.  *)

module Hlist (D:HashedType) :
  (S with type t = D.t list and type u = (D.t list -> D.t list)*(D.t->D.t))
(** Hashconsing of lists.  *)

module Hobj : (S with type t = Obj.t and type u = (Obj.t -> Obj.t) * unit)
(** Hashconsing of OCaml values. *)

end = struct
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Hash consing of datastructures *)

(* The generic hash-consing functions (does not use Obj) *)

(* [t] is the type of object to hash-cons
 * [u] is the type of hash-cons functions for the sub-structures
 *   of objects of type t (u usually has the form (t1->t1)*(t2->t2)*...).
 * [hashcons u x] is a function that hash-cons the sub-structures of x using
 *   the hash-consing functions u provides.
 * [eq] is a comparison function. It is allowed to use physical equality
 *   on the sub-terms hash-consed by the hashcons function.
 * [hash] is the hash function given to the Hashtbl.Make function
 *
 * Note that this module type coerces to the argument of Hashtbl.Make.
 *)

module type HashconsedType =
  sig
    type t
    type u
    val hashcons :  u -> t -> t
    val eq : t -> t -> bool
    val hash : t -> int
  end

(** The output is a function [generate] such that [generate args] creates a
    hash-table of the hash-consed objects, together with [hcons], a function
    taking a table and an object, and hashcons it. For simplicity of use, we use
    the wrapper functions defined below. *)

module type S =
  sig
    type t
    type u
    type table
    val generate : u -> table
    val hcons : table -> t -> t
    val stats : table -> Hashset.statistics
  end

module Make (X : HashconsedType) : (S with type t = X.t and type u = X.u) =
  struct
    type t = X.t
    type u = X.u

    (* We create the type of hashtables for t, with our comparison fun.
     * An invariant is that the table never contains two entries equals
     * w.r.t (=), although the equality on keys is X.eq. This is
     * granted since we hcons the subterms before looking up in the table.
     *)
    module Htbl = Hashset.Make(X)

    type table = (Htbl.t * u)

    let generate u =
      let tab = Htbl.create 97 in
      (tab, u)

    let hcons (tab, u) x =
      let y = X.hashcons u x in
      Htbl.repr (X.hash y) y tab

    let stats (tab, _) = Htbl.stats tab

  end

(* A few useful wrappers:
 * takes as argument the function [generate] above and build a function of type
 * u -> t -> t that creates a fresh table each time it is applied to the
 * sub-hcons functions. *)

(* For non-recursive types it is quite easy. *)
let simple_hcons h f u =
  let table = h u in
  fun x -> f table x

(* For a recursive type T, we write the module of sig Comp with u equals
 * to (T -> T) * u0
 * The first component will be used to hash-cons the recursive subterms
 * The second one to hashcons the other sub-structures.
 * We just have to take the fixpoint of h
 *)
let recursive_hcons h f u =
  let loop = ref (fun _ -> assert false) in
  let self x = !loop x in
  let table = h (self, u) in
  let hrec x = f table x in
  let () = loop := hrec in
  hrec

(* Basic hashcons modules for string and obj. Integers do not need be
   hashconsed.  *)

module type HashedType = sig type t val hash : t -> int end

(* list *)
module Hlist (D:HashedType) =
  Make(
    struct
      type t = D.t list
      type u = (t -> t) * (D.t -> D.t)
      let hashcons (hrec,hdata) = function
        | x :: l -> hdata x :: hrec l
        | l -> l
      let eq l1 l2 =
        l1 == l2 ||
          match l1, l2 with
          | [], [] -> true
          | x1::l1, x2::l2 -> x1==x2 && l1==l2
          | _ -> false
      let rec hash accu = function
      | [] -> accu
      | x :: l ->
        let accu = Hashset.Combine.combine (D.hash x) accu in
        hash accu l
      let hash l = hash 0 l
    end)

(* string *)
module Hstring = Make(
  struct
    type t = string
    type u = unit
    let hashcons () s =(* incr accesstr;*) s
    external eq : string -> string -> bool = "caml_string_equal" "noalloc"
    (** Copy from CString *)
    let rec hash len s i accu =
      if i = len then accu
      else
        let c = Char.code (String.unsafe_get s i) in
        hash len s (succ i) (accu * 19 + c)

    let hash s =
      let len = String.length s in
      hash len s 0 0
  end)

(* Obj.t *)
exception NotEq

(* From CAMLLIB/caml/mlvalues.h *)
let no_scan_tag = 251
let tuple_p obj = Obj.is_block obj && (Obj.tag obj < no_scan_tag)

let comp_obj o1 o2 =
  if tuple_p o1 && tuple_p o2 then
    let n1 = Obj.size o1 and n2 = Obj.size o2 in
      if n1=n2 then
        try
          for i = 0 to pred n1 do
            if not (Obj.field o1 i == Obj.field o2 i) then raise NotEq
          done; true
        with NotEq -> false
      else false
  else o1=o2

let hash_obj hrec o =
  begin
    if tuple_p o then
      let n = Obj.size o in
        for i = 0 to pred n do
          Obj.set_field o i (hrec (Obj.field o i))
        done
  end;
  o

module Hobj = Make(
  struct
    type t = Obj.t
    type u = (Obj.t -> Obj.t) * unit
    let hashcons (hrec,_) = hash_obj hrec
    let eq = comp_obj
    let hash = Hashtbl.hash
  end)

end


module HMap : sig 

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module type HashedType =
sig
  type t
  val compare : t -> t -> int
  (** Total ordering *)
  val hash : t -> int
  (** Hashing function compatible with [compare], i.e. [compare x y = 0] implies
      [hash x = hash y]. *)
end

(** Hash maps are maps that take advantage of having a hash on keys. This is
    essentially a hash table, except that it uses purely functional maps instead
    of arrays.

    CAVEAT: order-related functions like [fold] or [iter] do not respect the
    provided order anymore! It's your duty to do something sensible to prevent
    this if you need it. In particular, [min_binding] and [max_binding] are now
    made meaningless.
*)
module Make(M : HashedType) : CMap.ExtS with type key = M.t

end = struct 

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module type HashedType =
sig
  type t
  val compare : t -> t -> int
  val hash : t -> int
end

module SetMake(M : HashedType) =
struct
  (** Hash Sets use hashes to prevent doing too many comparison tests. They
      associate to each hash the set of keys having that hash.

      Invariants:

      1. There is no empty set in the intmap.
      2. All values in the same set have the same hash, which is the int to
         which it is associated in the intmap.
  *)

  module Set = Set.Make(M)

  type elt = M.t

  type t = Set.t Int.Map.t

  let empty = Int.Map.empty

  let is_empty = Int.Map.is_empty

  let mem x s =
    let h = M.hash x in
    try
      let m = Int.Map.find h s in
      Set.mem x m
    with Not_found -> false

  let add x s =
    let h = M.hash x in
    try
      let m = Int.Map.find h s in
      let m = Set.add x m in
      Int.Map.update h m s
    with Not_found ->
      let m = Set.singleton x in
      Int.Map.add h m s

  let singleton x =
    let h = M.hash x in
    let m = Set.singleton x in
    Int.Map.singleton h m

  let remove x s =
    let h = M.hash x in
    try
      let m = Int.Map.find h s in
      let m = Set.remove x m in
      if Set.is_empty m then
        Int.Map.remove h s
      else
        Int.Map.update h m s
    with Not_found -> s

  let height s = Int.Map.height s

  let is_smaller s1 s2 = height s1 <= height s2 + 3

  (** Assumes s1 << s2 *)
  let fast_union s1 s2 =
    let fold h s accu =
      try Int.Map.modify h (fun _ s' -> Set.fold Set.add s s') accu
      with Not_found -> Int.Map.add h s accu
    in
    Int.Map.fold fold s1 s2

  let union s1 s2 =
    if is_smaller s1 s2 then fast_union s1 s2
    else if is_smaller s2 s1 then fast_union s2 s1
    else
      let fu _ m1 m2 = match m1, m2 with
      | None, None -> None
      | (Some _ as m), None | None, (Some _ as m) -> m
      | Some m1, Some m2 -> Some (Set.union m1 m2)
      in
      Int.Map.merge fu s1 s2

  (** Assumes s1 << s2 *)
  let fast_inter s1 s2 =
    let fold h s accu =
      try
        let s' = Int.Map.find h s2 in
        let si = Set.filter (fun e -> Set.mem e s') s in
        if Set.is_empty si then accu
        else Int.Map.add h si accu
     with Not_found -> accu
    in
    Int.Map.fold fold s1 Int.Map.empty

  let inter s1 s2 =
    if is_smaller s1 s2 then fast_inter s1 s2
    else if is_smaller s2 s1 then fast_inter s2 s1
    else
      let fu _ m1 m2 = match m1, m2 with
      | None, None -> None
      | Some _, None | None, Some _ -> None
      | Some m1, Some m2 ->
        let m = Set.inter m1 m2 in
        if Set.is_empty m then None else Some m
      in
      Int.Map.merge fu s1 s2

  (** Assumes s1 << s2 *)
  let fast_diff_l s1 s2 =
    let fold h s accu =
      try
        let s' = Int.Map.find h s2 in
        let si = Set.filter (fun e -> not (Set.mem e s')) s in
        if Set.is_empty si then accu
        else Int.Map.add h si accu
     with Not_found -> Int.Map.add h s accu
    in
    Int.Map.fold fold s1 Int.Map.empty

  (** Assumes s2 << s1 *)
  let fast_diff_r s1 s2 =
    let fold h s accu =
      try
        let s' = Int.Map.find h accu in
        let si = Set.filter (fun e -> not (Set.mem e s)) s' in
        if Set.is_empty si then Int.Map.remove h accu
        else Int.Map.update h si accu
     with Not_found -> accu
    in
    Int.Map.fold fold s2 s1

  let diff s1 s2 =
    if is_smaller s1 s2 then fast_diff_l s1 s2
    else if is_smaller s2 s2 then fast_diff_r s1 s2
    else
      let fu _ m1 m2 = match m1, m2 with
      | None, None -> None
      | (Some _ as m), None -> m
      | None, Some _ -> None
      | Some m1, Some m2 ->
        let m = Set.diff m1 m2 in
        if Set.is_empty m then None else Some m
      in
      Int.Map.merge fu s1 s2

  let compare s1 s2 = Int.Map.compare Set.compare s1 s2

  let equal s1 s2 = Int.Map.equal Set.equal s1 s2

  let subset s1 s2 =
    let check h m1 =
      let m2 = try Int.Map.find h s2 with Not_found -> Set.empty in
      Set.subset m1 m2
    in
    Int.Map.for_all check s1

  let iter f s =
    let fi _ m = Set.iter f m in
    Int.Map.iter fi s

  let fold f s accu =
    let ff _ m accu = Set.fold f m accu in
    Int.Map.fold ff s accu

  let for_all f s =
    let ff _ m = Set.for_all f m in
    Int.Map.for_all ff s

  let exists f s =
    let fe _ m = Set.exists f m in
    Int.Map.exists fe s

  let filter f s =
    let ff m = Set.filter f m in
    let s = Int.Map.map ff s in
    Int.Map.filter (fun _ m -> not (Set.is_empty m)) s

  let partition f s =
    let fold h m (sl, sr) =
      let (ml, mr) = Set.partition f m in
      let sl = if Set.is_empty ml then sl else Int.Map.add h ml sl in
      let sr = if Set.is_empty mr then sr else Int.Map.add h mr sr in
      (sl, sr)
    in
    Int.Map.fold fold s (Int.Map.empty, Int.Map.empty)

  let cardinal s =
    let fold _ m accu = accu + Set.cardinal m in
    Int.Map.fold fold s 0

  let elements s =
    let fold _ m accu = Set.fold (fun x accu -> x :: accu) m accu in
    Int.Map.fold fold s []

  let min_elt _ = assert false (** Cannot be implemented efficiently *)

  let max_elt _ = assert false (** Cannot be implemented efficiently *)

  let choose s =
    let (_, m) = Int.Map.choose s in
    Set.choose m

  let split s x = assert false (** Cannot be implemented efficiently *)

end

module Make(M : HashedType) =
struct
  (** This module is essentially the same as SetMake, except that we have maps
      instead of sets in the intmap. Invariants are the same. *)
  module Set = SetMake(M)
  module Map = CMap.Make(M)

  type key = M.t

  type 'a t = 'a Map.t Int.Map.t

  let empty = Int.Map.empty

  let is_empty = Int.Map.is_empty

  let mem k s =
    let h = M.hash k in
    try
      let m = Int.Map.find h s in
      Map.mem k m
    with Not_found -> false

  let add k x s =
    let h = M.hash k in
    try
      let m = Int.Map.find h s in
      let m = Map.add k x m in
      Int.Map.update h m s
    with Not_found ->
      let m = Map.singleton k x in
      Int.Map.add h m s

  let singleton k x =
    let h = M.hash k in
    Int.Map.singleton h (Map.singleton k x)

  let remove k s =
    let h = M.hash k in
    try
      let m = Int.Map.find h s in
      let m = Map.remove k m in
      if Map.is_empty m then
        Int.Map.remove h s
      else
        Int.Map.update h m s
    with Not_found -> s

  let merge f s1 s2 =
    let fm h m1 m2 = match m1, m2 with
    | None, None -> None
    | Some m, None ->
      let m = Map.merge f m Map.empty in
      if Map.is_empty m then None
      else Some m
    | None, Some m ->
      let m = Map.merge f Map.empty m in
      if Map.is_empty m then None
      else Some m
    | Some m1, Some m2 ->
      let m = Map.merge f m1 m2 in
      if Map.is_empty m then None
      else Some m
    in
    Int.Map.merge fm s1 s2

  let compare f s1 s2 =
    let fc m1 m2 = Map.compare f m1 m2 in
    Int.Map.compare fc s1 s2

  let equal f s1 s2 =
    let fe m1 m2 = Map.equal f m1 m2 in
    Int.Map.equal fe s1 s2

  let iter f s =
    let fi _ m = Map.iter f m in
    Int.Map.iter fi s

  let fold f s accu =
    let ff _ m accu = Map.fold f m accu in
    Int.Map.fold ff s accu

  let for_all f s =
    let ff _ m = Map.for_all f m in
    Int.Map.for_all ff s

  let exists f s =
    let fe _ m = Map.exists f m in
    Int.Map.exists fe s

  let filter f s =
    let ff m = Map.filter f m in
    let s = Int.Map.map ff s in
    Int.Map.filter (fun _ m -> not (Map.is_empty m)) s

  let partition f s =
    let fold h m (sl, sr) =
      let (ml, mr) = Map.partition f m in
      let sl = if Map.is_empty ml then sl else Int.Map.add h ml sl in
      let sr = if Map.is_empty mr then sr else Int.Map.add h mr sr in
      (sl, sr)
    in
    Int.Map.fold fold s (Int.Map.empty, Int.Map.empty)

  let cardinal s =
    let fold _ m accu = accu + Map.cardinal m in
    Int.Map.fold fold s 0

  let bindings s =
    let fold _ m accu = Map.fold (fun k x accu -> (k, x) :: accu) m accu in
    Int.Map.fold fold s []

  let min_binding _ = assert false (** Cannot be implemented efficiently *)

  let max_binding _ = assert false (** Cannot be implemented efficiently *)

  let fold_left _ _ _ = assert false (** Cannot be implemented efficiently *)

  let fold_right _ _ _ = assert false (** Cannot be implemented efficiently *)

  let choose s =
    let (_, m) = Int.Map.choose s in
    Map.choose m

  let find k s =
    let h = M.hash k in
    let m = Int.Map.find h s in
    Map.find k m

  let get k s = try find k s with Not_found -> assert false

  let split k s = assert false (** Cannot be implemented efficiently *)

  let map f s =
    let fs m = Map.map f m in
    Int.Map.map fs s

  let mapi f s =
    let fs m = Map.mapi f m in
    Int.Map.map fs s

  let modify k f s =
    let h = M.hash k in
    let m = Int.Map.find h s in
    let m = Map.modify k f m in
    Int.Map.update h m s

  let bind f s =
    let fb m = Map.bind f m in
    Int.Map.map fb s

  let domain s = Int.Map.map Map.domain s

  let update k x s =
    let h = M.hash k in
    let m = Int.Map.find h s in
    let m = Map.update k x m in
    Int.Map.update h m s

  let smartmap f s =
    let fs m = Map.smartmap f m in
    Int.Map.smartmap fs s

  let smartmapi f s =
    let fs m = Map.smartmapi f m in
    Int.Map.smartmap fs s

  let height s = Int.Map.height s

  module Unsafe =
  struct
    let map f s =
      let fs m = Map.Unsafe.map f m in
      Int.Map.map fs s
  end

  module Monad(M : CMap.MonadS) =
  struct
    module IntM = Int.Map.Monad(M)
    module ExtM = Map.Monad(M)

    let fold f s accu =
      let ff _ m accu = ExtM.fold f m accu in
      IntM.fold ff s accu

    let fold_left _ _ _ = assert false
    let fold_right _ _ _ = assert false
  end

end

end


module Names = struct
  module DirPath = struct
    type t = string
    let equal = (=)
    let compare = compare
    let table = Hashcons.Hstring.generate ()
    let hcons = Hashcons.Hstring.hcons table
    let rec hash len s i accu =
      if i = len then accu
      else
        let c = Char.code (String.unsafe_get s i) in
        hash len s (succ i) (accu * 19 + c)
    let hash s =
      let len = String.length s in
      hash len s 0 0
    let to_string x = x
    let make s = hcons s
  end
end

include CSig
module List = CList
module Array = CArray
