% Some simple operations on lists.

module	lists.

kind  pairty   type -> type -> type.

type  pair     A -> B -> (pairty A B).

type  id       (list A) -> (list A) -> o.
type  memb     A -> (list A) -> o.
type  member   A -> (list A) -> o.
type  append   (list A) -> (list A) -> (list A) -> o.
type  join     (list A) -> (list A) -> (list A) -> o.
type  assoc    A -> B -> (list (pairty A B)) -> o.
type  domain   (list (pairty A B)) -> (list A) -> o.
type  range   (list (pairty A B)) -> (list B) -> o.

id nil nil.
id (X::L) (X::K) :- id L K.

memb X (X::L).
memb X (Y::L) :- memb X L.

member X (X::L) :- !.
member X (Y::L) :- member X L.

append nil K K.
append (X::L) K (X::M) :- append L K M.

join nil K K.
join (X::L) K M :- memb X K, !, join L K M.
join (X::L) K (X::M) :- join L K M.

assoc X Y (pair X Y::L).
assoc X Y (P::L) :- assoc X Y L.

domain nil nil.
domain (pair X Y::Alist) (X::L) :- domain Alist L.

range nil nil.
range (pair X Y::Alist) (Y::L) :- range Alist L.
