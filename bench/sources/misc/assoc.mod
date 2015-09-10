module assoc.

accumulate assoclists. 

kind pair   type -> type -> type.

type pair   A -> B -> (pair A B).

type assoc  A -> B -> (list (pair A B)) -> o.

(assoc X Y L) :- (memb (pair X Y) L).
