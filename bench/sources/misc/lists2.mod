module  lists2.

type append  (list A) -> (list A) -> (list A) -> o.

type reverse (list A) -> (list A) -> o.

type cons   A -> (list A) -> (list A).

type null   (list A).


append null L L.
(append (cons X L1) L2 (cons X L3)) :- (append L1 L2 L3). 

reverse null null.
(reverse (cons X L1) L2) :- (reverse L1 L3), (append L3 (cons X null) L2).
