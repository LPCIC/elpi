module reduce_cbn_nocopy.

cbn (lam F) (lam F2) :- !, pi x\cbn x x => cbn (F x) (F2 x).
cbn (app (lam F) N) M :- !, cbn (F N) M.
cbn (app M N) R :- cbn M (lam F), !, cbn (app (lam F) N) R.
cbn (app X Y) (app X2 Y2) :- cbn X X2, cbn Y Y2.

main :-
 (ZERO = lam s\ lam z\ z),
 (SUCC = lam n\ lam s\ lam z\ app s (app (app n s) z)),
 cbn (app SUCC ZERO) ONE,
 (PLUS = lam n\ lam m\ lam s\ lam z\ app (app n s) (app (app m s) z)),
 (MULT = lam n\ lam m\ lam s\ app n (app m s)),
 cbn (app SUCC (app SUCC ZERO)) TWO,
 cbn (app (app PLUS (app (app PLUS TWO) TWO)) TWO) SIX,
 cbn (app (app MULT SIX) TWO) TWELVE,
 (EXP = lam n\ lam m\ app n m),
 cbn (app (app PLUS TWO) ONE) THREE,
 cbn (app (app EXP TWO) THREE) NINE,
 cbn (app (app MULT TWO) TWO) FOUR,
 cbn (app (app PLUS THREE) TWO) FIVE,
 cbn (app (app PLUS FOUR) TWO) SIX,
 cbn (app (app EXP FIVE) FIVE) RES,
 cbn (app (app EXP FIVE) FIVE) RES,
 cbn (app (app EXP FIVE) FIVE) RES,
 cbn (app (app EXP FIVE) FIVE) RES,
 cbn (app (app EXP FIVE) FIVE) RES,
 cbn (app (app EXP FIVE) FIVE) RES.
