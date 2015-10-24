module milner_mycroft.

infixr !! 145.
infixr --> 145.

lam F !! A --> B :- pi x\ x !! A => F x !! B.

app F G !! B :- F !! A --> B, G !! A.

/* Bacata
letrec (f \ [BO f,REST f]) !! B :-
 (pi f\ (pi X \ f !! A X) => ((pi x\ BO f !! A x), REST f !! B)),
 $print f ":" A.*/

/* Bacata, stampe per capirci */
letrec (f \ [BO f,REST f]) !! B :-
 (pi f\ (pi X \ f !! A X) => ((pi x\ (BO f !! (R x), $print "R = " R, $print (R x) "===" (A x), R x = A x, $print A)), REST f !! B)),
 $print f ":" A.

% Tests

0 !! nat.
plus !! nat --> nat --> nat.

test1 X :- letrec (f\ [0,0]) !! X.
test2 X :- letrec (f\ [(lam x\ app (app plus x) x),0]) !! X.
test3 X :- letrec (f\ [(lam x\ app (app plus x) x),app f 0]) !! X.
% BIG BUG IN test4: A^0 = x0\ X0 x1 --> X0 x1   :-(
test4 X :- letrec (f\ [(lam x\ x),0]) !! X.
test5 X :- letrec (f\ [(lam x\ x),app f 0]) !! X.
