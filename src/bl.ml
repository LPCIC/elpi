(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

type 'a t = BNil | BCons of { mutable head : 'a; mutable last : 'a t; mutable tail : 'a t }

let rec pp pp_a fmt = function
  | BNil -> Format.fprintf fmt "[]"
  | BCons { head; tail; last } as x ->
      Format.fprintf fmt "[self %x, tail %x, last %x] %a :: "
        (Obj.magic x land 0xffffff)
        (Obj.magic tail land 0xffffff)
        (Obj.magic last land 0xffffff)
        pp_a head;
      pp pp_a fmt tail

let show pp_a x = Format.asprintf "%a" (pp pp_a) x

type 'a l = Nil | Cons of { head : 'a; last : unit; tail : 'a l } [@@deriving show, ord]

let empty () = BNil

let cons head tail =
  match tail with
  | BNil ->
      let rec last = BCons { head; tail; last } in
      last
  | BCons { last } -> BCons { head; tail; last }

let set_last_tail l = function
  | BCons x ->
      assert (x.tail = BNil);
      (* Format.eprintf "set tail of %d to %d \n" (Obj.magic w) (Obj.magic l);  *)
      x.tail <- l
  | BNil -> Elpi_util.Util.anomaly "blist: can't rcons after commit"

let rcons head tail =
  match tail with
  | BNil ->
      let rec last = BCons { head; tail = BNil; last } in
      last
  | BCons b ->
      let rec last = BCons { head; tail = BNil; last } in
      let olast = b.last in
      b.last <- last;
      set_last_tail last olast;
      tail

let rec replace f x = function
  | BNil -> assert false
  | BCons ({ head; tail } as b) when f head -> b.head <- x
  | BCons { tail } -> replace f x tail

let rec insert_before f x = function
  | BNil -> assert false (*let rec last = BCons { head = x; last; tail = BNil } in last*)
  | BCons { head; last } as l when f head -> BCons { head = x; last; tail = l }
  | BCons { head; last; tail } -> BCons { head; last; tail = insert_before f x tail }

let insert_after f x = function
  | BNil -> assert false
  | BCons b0 as l ->
      let rec insert_after_aux = function
        | BNil -> assert false
        | BCons ({ head; last; tail } as b) when f head ->
            let new_tail = BCons { head = x; last; tail } in
            if tail == BNil then b0.last <- new_tail;
            b.tail <- new_tail
        | BCons { tail } -> insert_after_aux tail
      in
      insert_after_aux l

let commit l = Obj.magic l

let commit_map f l : 'b l =
  let rec commit = function
    | BNil -> ()
    | BCons ({ head; last; tail } as x) ->
        x.head <- Obj.magic @@ f head;
        x.last <- BNil;
        commit tail
  in
  commit l;
  Obj.magic l

let rec to_list = function Nil -> [] | Cons { head; tail } -> head :: to_list tail
