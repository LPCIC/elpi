infixl ' 139.
infixl ==> 149.

term (lam F) (impl A B) :- pi x\ term x A => term (F x) B.
term (F ' T) B :- term T A, term F (impl A B).
term eq (impl A (impl A bool)).

/* r, t Y C1 C2, i P C1 C2, b, c C1 C2, k C, s C1 C2, d */

thm G C :- $print "|- " G " := " C, fail.
thm G C :- is_flex C, !, $delay (thm G C) C.
thm G C :- thm_ G C.

thm_ (eq ' X ' X) r :- term X A.
thm_ (eq ' X ' Z) (t Y C1 C2) :-
 term X A, term Y A, term Z A,
 thm (eq ' X ' Y) C1, thm (eq ' Y ' Z) C2.
thm_ Q (i P C1 C2) :- thm (eq ' P ' Q) C1, thm P C2.
thm_ (eq ' ((lam F) ' X) ' (F X)) b :-
 term X A,
 (pi y\ term y A => term (F y) B).
thm_ (eq ' (F ' X) ' (G ' Y)) (c C1 C2) :-
 term X A, term Y A,
 (pi y\ term y A => term (F y) B),
 (pi y\ term y A => term (G y) B),
 thm (eq ' X ' Y) C1, thm (eq ' F ' G) C2.
thm_ (eq ' (lam S) ' (lam T)) (k C) :-
 (pi y\ term y A => term (S y) B),
 (pi y\ term y A => term (T y) B),
 (pi x\ term x A => thm (eq ' (S x) ' (T x)) C).
thm_ (eq ' P ' Q) (s C1 C2) :-
 term P bool, term Q bool, /* CSC: check if required */
 (pi c\ thm P c => thm Q (C1 c)),
 (pi c\ thm Q c => thm P (C2 c)).

thm (eq C A) d :-
 def1 C A./*,
 pi T\ ttype T => (ttype (B T), term A (B T)).

def1 id (lam x\ x).*/

def1 tt (eq ' (lam x\ x) ' (lam x\ x)).
