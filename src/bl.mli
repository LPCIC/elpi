(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

(* These lists become functional only after a call to commit. Before that
   they are imperative, keeping a pointer to an old "copy" must be avoided.
   Before calling commit rcons is O(1) time and space. *)

type 'a t
val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
val show : (Format.formatter -> 'a -> unit) -> 'a t -> string

(* These 4 are O(1) *)
val empty : unit -> 'a t
val single : 'a -> 'a t
val cons : 'a -> 'a t -> 'a t
val rcons : 'a -> 'a t -> 'a t

(* O(n) spaec and time *)
val copy : 'a t -> 'a t

(* These 3 are O(n) time, O(1) space. The test must succeed once *)
val replace : ('a -> bool) -> 'a -> 'a t -> unit
val insert_before : ('a -> bool) -> 'a -> 'a t -> 'a t
val insert_after : ('a -> bool) -> 'a -> 'a t -> unit

type  'a l = Nil | Cons of { head : 'a; tail : 'a l; last : unit; }
val pp_l : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a l -> unit
val show_l : (Format.formatter -> 'a -> unit) -> 'a l -> string

(* no more rcons, O(1) time and space *)
val commit : 'a t -> 'a l

(* no more rcons, O(n) time, O(1) space *)
val commit_map : ('a -> 'b) -> 'a t -> 'b l

(* allocates a new list, O(n) time and space *)
val to_list : 'a l -> 'a list
val to_list_map : ('a -> 'b) -> 'a l -> 'b list

val iter : ('a -> unit) -> 'a l -> unit
val of_list : 'a list -> 'a l
val length : 'a l -> int
val flatten : 'a l list -> 'a l
val sort : ('a -> 'a -> int) -> 'a l -> 'a l
val rev : 'a l -> 'a l
