(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

type 'a t =
  | BNil
  | BCons of { mutable head : 'a; mutable tail : 'a t; mutable last : 'a t; }
  (* | UndoRcons of { old_tail : 'a data; next : 'a t }
  | UndoInsert of { old_before : 'a data; old_after : 'a data; next : 'a t } *)
(* and 'a t = 'a data ref *)

let pp_pointer fmt x = Format.fprintf fmt "%x" (Obj.magic x land 0xffffff)
let rec pp pp_a fmt = function
  | BNil -> Format.fprintf fmt "[]"
  | BCons { head; tail; last } as x ->
      Format.fprintf fmt "[self %a, tail %a, last %a] %a :: "
        pp_pointer x
        pp_pointer tail
        pp_pointer last
        pp_a head;
      pp pp_a fmt tail
  (* | UndoRcons { old_tail; next } -> Format.fprintf fmt "UndoRcons %a :: " pp_pointer old_tail ; pp pp_a fmt next
  | UndoInsert { old_before; old_after; next } -> Format.fprintf fmt "UndoInsert %a - %a :: " pp_pointer old_before pp_pointer old_after; pp pp_a fmt next *)

let show pp_a x = Format.asprintf "%a" (pp pp_a) x

type 'a l = Nil | Cons of { head : 'a; tail : 'a l; last : unit; }
[@@deriving show]
let empty () = BNil

let cons head tail =
  match tail with
  | BNil ->
      let rec last = BCons { head; tail; last } in
      last
  | BCons { last } -> BCons { head; tail; last }

let single x = cons x (empty ())

let set_last_tail l = function
  | BCons x ->
      assert (x.tail = BNil);
      (* Format.eprintf "set tail of %d to %d \n" (Obj.magic w) (Obj.magic l);  *)
      x.tail <- l
  | BNil -> Elpi_util.Util.anomaly "blist: can't rcons after commit"
let set_last l = function
  | BCons x ->  x.last <- l
  | BNil -> assert false

let copy = function
  | BNil -> BNil
  | BCons { head; tail; last } as l ->
      let x = ref last in
      let rec aux = function
        | BNil -> BNil
        | BCons { head; tail = BNil; last } -> let rec last = BCons { head; tail = BNil; last = last } in x := last; last
        | BCons { head; tail; last } -> BCons { head; tail = aux tail; last = BNil }
      in
      let l = aux l in
      set_last !x l;
      l

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
  | BNil -> ()
  | BCons ({ head; tail } as b) when f head -> b.head <- x
  | BCons { tail } -> replace f x tail
let replace f x l = replace f x l; l

let rec insert_before f x = function
  | BNil -> BNil
  | BCons { head; last } as l when f head -> BCons { head = x; last; tail = l }
  | BCons { head; last; tail } -> BCons { head; last; tail = insert_before f x tail }

let insert_after f x = function
  | BNil -> ()
  | BCons b0 as l ->
      let rec insert_after_aux = function
        | BNil -> ()
        | BCons ({ head; last; tail } as b) when f head ->
            let new_tail = BCons { head = x; last; tail } in
            if tail == BNil then b0.last <- new_tail;
            b.tail <- new_tail
        | BCons { tail } -> insert_after_aux tail
      in
      insert_after_aux l
let insert_after f x l = insert_after f x l; l

let rec iter f = function Nil -> () | Cons { head; tail } -> f head; iter f tail
let rec of_list = function
  | [] -> Nil
  | x :: xs -> Cons { head = x; last = (); tail = of_list xs }

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
let rec to_list_map f = function Nil -> [] | Cons { head; tail } -> f head :: to_list_map f tail

(* what follows is an adaptation of OCaml's standard library *)

(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

let rec length_aux n = function Nil -> n | Cons { tail } -> length_aux (n+1) tail
let length l = length_aux 0 l

let rec append  l1 l2 =
  match l1 with
  | Nil -> l2
  | Cons { head; tail; last } -> Cons { head; last; tail = append tail l2 }

let rec rev_append l1 l2 =
  match l1 with
  | Nil -> l2
  | Cons { head; last; tail } -> rev_append tail (Cons { head; last; tail = l2 })

let rev l = rev_append l Nil
  
let rec flatten = function
| [] -> Nil
| head :: tail -> append head @@ flatten tail

let sort cmp l =
  let rec rev_merge l1 l2 accu =
    match l1, l2 with
    | Nil, l2 -> rev_append l2 accu
    | l1, Nil -> rev_append l1 accu
    | Cons { head = h1; tail = t1 }, Cons { head = h2; tail = t2 } ->
        if cmp h1 h2 <= 0
        then rev_merge t1 l2 (Cons { head = h1; tail = accu; last = ()})
        else rev_merge l1 t2 (Cons { head = h2; tail = accu; last = ()})
  in
  let rec rev_merge_rev l1 l2 accu =
    match l1, l2 with
    | Nil, l2 -> rev_append l2 accu
    | l1, Nil -> rev_append l1 accu
    | Cons { head = h1; tail = t1 }, Cons { head = h2; tail = t2 } ->
        if cmp h1 h2 > 0
        then rev_merge_rev t1 l2 (Cons { head = h1; tail = accu; last = ()})
        else rev_merge_rev l1 t2 (Cons { head = h2; tail = accu; last = ()})
  in
  let rec sort n l =
    match n, l with
    | 1, x -> x, Nil
    | 2, Cons { head = x1; tail = Cons { head = x2 ; tail = tl } } ->
      let s = if cmp x1 x2 <= 0 then Cons { head = x1; tail = Cons { head = x2 ; tail = Nil; last = () }; last = () } else Cons { head = x2; tail = Cons { head = x1 ; tail = Nil; last = () }; last = () } in
      (s, tl)
    | _ ->
        let n1 = n asr 1 in
        let n2 = n - n1 in
        let s1, l2 = rev_sort n1 l in
        let s2, tl = rev_sort n2 l2 in
        (rev_merge_rev s1 s2 Nil, tl)
  and rev_sort n l =
    match n, l with
    | 1, x -> x, Nil
    | 2, Cons { head = x1; tail = Cons { head = x2 ; tail = tl } } ->
        let s = if cmp x1 x2 > 0 then Cons { head = x1; tail = Cons { head = x2 ; tail = Nil; last = () }; last = () } else Cons { head = x2; tail = Cons { head = x1 ; tail = Nil; last = () }; last = () } in
        (s, tl)
    | _ ->
        let n1 = n asr 1 in
        let n2 = n - n1 in
        let s1, l2 = sort n1 l in
        let s2, tl = sort n2 l2 in
        (rev_merge s1 s2 Nil, tl)
  in
  let len = length l in
  if len < 2 then l else fst (sort len l)
