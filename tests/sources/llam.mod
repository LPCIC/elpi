module llam.

type spy o -> o.
spy X :- % $print "test " X, 
  not(not(X)).

kind t type.
type test ((t -> t -> o) -> A -> o) -> A -> o.

test P T :-
  spy(P (x\y\x = y) F, F = T),
  spy(P (x\y\y = x) F, F = T),
  spy(pi dummy\ sigma F\ P (x\y\x = y) F, F = T),
  spy(pi dummy\ sigma F\ P (x\y\y = x) F, F = T).

type clause (t -> t -> t) -> o.
type clause1 (t -> t -> t) -> o.
type clause2 (t -> t -> pair t t) -> o.
type pr A -> B -> pair A B.
type pr A -> B -> pair A B.
kind pair type -> type -> type.

clause (x\y\F y x) :- F = a\b\b.
clause1 (x\y\x).
clause2 (x\y\pr (X x) (F y (X x))) :- F = a\b\b.

type whatever t -> t.
type h t -> t -> t.
type r (t -> t) -> t.

main :-
  test (eq\F\        pi x\ pi y\ eq (F y x) x)             (a\b\b),
  test (eq\F\   not (pi x\ pi y\ eq (F x) y))              whatever,
  test (eq\F\        pi x\ pi y\ eq (F y x) (r (w\h w x))) (a\b\r (x\h x b)),
  test (eq\F\        pi x\ pi y\ sigma R\ R = x, eq (F y x) R)             (a\b\b),
  test (eq\F\   not (pi x\ pi y\ sigma R\ R = x, eq (F R) y))              whatever,
  test (eq\F\        pi x\ pi y\ sigma R\ R = x, eq (F y x) (r (w\h w R))) (a\b\r (x\h x b)),
  (pi dummy\ clause (x\y\x)),
  (pi dummy\ clause1 (x\y\F y x), F = a\b\b),
  (pi dummy\ clause2 (x\y\pr x x)),
  true.
