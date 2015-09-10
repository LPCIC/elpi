module assoclists.

type memb A -> list A -> o.

type append  (list A) -> (list A) -> (list A) -> o.

type reverse (list A) -> (list A) -> o.

memb X (X::L) :- !.
memb X (Y::L) :- memb X L.

append nil L L.
append (X::L1) L2 (X::L3) :- append L1 L2 L3.


reverse nil nil.
reverse (X::L1) L2 :- reverse L1 L3, append L3 [X] L2.

