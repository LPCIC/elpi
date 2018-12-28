module lambda3.

of (appl T1 T2) B :- of T1 (impl A B), of T2 A.
of (lam F) (impl A B) :- pi x\ of x A => of (F x) B.

append (xcons X XS) L (xcons X L1)  :- append XS L L1 .
append xnil L L .

termify xnil (lam x\x).
termify (xcons X XS) (lam F) :- pi c\ termify XS (F c).

test L :- 
  X1 = (xcons x0 (xcons x1 (xcons x2 (xcons x3 (xcons x4 (xcons x5 (xcons x6 (xcons x7 (xcons x8 (xcons x9 (xcons x10 xnil))))))))))), 
  append X1 X1 X2 ,
  append X2 X2 X3 ,
  append X3 X3 X4 ,
  append X4 X4 X5 ,
  append X5 X5 X6 ,
  % append X6 X6 X7 ,
  % append X7 X7 X8 ,
  % append X8 X8 X9 ,
  % append X9 X9 X10 ,
  % append X10 X10 X11 ,
  % append X11 X11 X12 ,
  % append X12 X12 X13 ,
  % append X13 X13 X14 ,
   % append X14 X14 X15 ,
   % append X15 X15 X16 ,
   % append X16 X16 X17 ,
   % append X17 X17 X18 ,
   X = X6 ,
   termify X L.

once L :- of L Z.

iter zero X.
iter (s N) X :- X, iter N X.

plus zero X X.
plus (s X) Y (s S) :- plus X Y S.

mult zero X zero.
mult (s X) Y Z :- mult X Y K, plus Y K Z.

exp zero X (s zero).
exp (s X) Y Z :- exp X Y K, mult Y K Z.

main :-
 TEN = s (s (s (s (s (s (s (s (s (s zero))))))))),
 exp (s (s (s zero))) TEN THOUSAND,
 test L,
 iter THOUSAND (once L).
