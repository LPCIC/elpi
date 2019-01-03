/* File listmanip.sig. Various simple list manipulation programs
needed for writing our theorem provers are defined here.  All of these
programs are essentially first-order and correspond to code one would
write in normal Prolog.  */

module listmanip.

type    member                  A -> (list A) -> o.
type    member_and_rest         A -> (list A) -> (list A) -> o.
type    nth_item                int -> A -> (list A) -> o.
type    nth_item_and_rest       int -> A -> (list A) -> (list A) -> o.
type    member_move_to_end      A -> (list A) -> (list A) -> o.
type    add_to_end              A -> (list A) -> (list A) -> o.

member X (X::L) :- !.
member X (Y::L) :- member X L.

member_and_rest A (A::Rest) Rest.
member_and_rest A (B::Tail) (B::Rest) :-
  member_and_rest A Tail Rest.

nth_item 0 A List :- !, member A List.
nth_item 1 A (A::Rest) :- !.
nth_item N A (B::Tail) :-
  (N1 is (N - 1)), nth_item N1 A Tail.

nth_item_and_rest 0 A List Rest :- !,
  member_and_rest A List Rest.
nth_item_and_rest 1 A (A::Rest) Rest.
nth_item_and_rest N A (B::Tail) (B::Rest) :-
  (N1 is (N - 1)),
  nth_item_and_rest N1 A Tail Rest.

member_move_to_end A (A::Rest) NewList :-
  add_to_end A Rest NewList.
member_move_to_end A (B::Tail) (B::NewList) :-
  member_move_to_end A Tail NewList.

add_to_end A nil (A::nil).
add_to_end A (Head::Tail) (Head::NewTail) :-
  add_to_end A Tail NewTail.


