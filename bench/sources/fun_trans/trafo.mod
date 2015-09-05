module trafo.

accumulate terms.

curry (lam (x\ F (fst x) (snd x)))
      (lam (x1\ lam (x2\ F x1 x2))).

curry (rec (f\ x\ F (fst x) (snd x) (p1\ p2\ app f (pair p1 p2))))
      (rec (f\ x1\ lam (x2\ F x1 x2 (y1\ y2\ app (app f y1) y2)))).
