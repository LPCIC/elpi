module mu.

ge (s X) zero.


mu :- theorem (xcons m (xcons u (xcons i (xcons i (xcons u xnil))))) (s (s (s (s (s zero))))) Dummy, !.

theorem (xcons m (xcons i xnil)) Dummy (xcons2 (xcons a (xcons m (xcons i xnil))) xnil2).
theorem R Depth (xcons2 (xcons N R) P) :-
    ge Depth zero,
    (s D) = Depth,
    theorem S D P,
    xrule N S R.

xrule (s zero) S R :- xrule1 S R.
xrule (s (s zero)) S R :- xrule2 S R.
xrule (s (s (s zero))) S R :- xrule3 S R.
xrule (s (s (s (s zero)))) S R :- xrule4 S R.

xrule1 (xcons i xnil) (xcons i (xcons u xnil)).
xrule1 (xcons H X) (xcons H Y) :-
    xrule1 X Y.

xrule2 (xcons m X) (xcons m Y) :- 
    append X X Y.

xrule3 (xcons i (xcons i (xcons i X))) (xcons u X).
xrule3 (xcons H X) (xcons H Y) :-
    xrule3 X Y.

xrule4 (xcons u (xcons u X)) X.
xrule4 (xcons H X) (xcons H Y) :-
    xrule4 X Y.

append xnil X X.
append (xcons A B) X (xcons A B1) :-
    append B X B1.

once :- mu.

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
 exp (s (s (s (s zero)))) TEN TENTHOUSAND,
 iter TENTHOUSAND once.
