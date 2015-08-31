% 29 july 2014.
sig lists.

type append                    	list A -> list A -> list A -> o.
type foreach			(A -> o) -> list A -> o.
type forsome			(A -> o) -> list A -> o.
type memb_and_rest A -> list A -> list A -> o.
type reverse                    list A -> list A -> o.
type member A -> list A -> o.
type foldl (A -> B -> B -> o) -> list A -> B -> B -> o.
type length list A -> int -> o.

type normalize    o -> o.
