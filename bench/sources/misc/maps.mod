%   Predicates in Lambda Prolog that define some of the `higher-order'
%   mapping operations

module	maps.

father jane moses.
father john peter.
father jane john.
father james peter.
father peter charles.

mapfun nil F nil.
mapfun [X|L] F [(F X)|K] :- mapfun L F K.

mappred nil P nil.
mappred (X::L) P (Y::K) :- P X Y, mappred L P K.


reduce_pred (W::nil) P F Y :- P W Y.
reduce_pred (W::L) P F (F Y Z) :- P W Y, reduce_pred L P F Z.

reduce nil F X X.
reduce (W::L) F X (F W Y) :-  reduce L F X Y.

reduce_eval L F Y Z :- reduce L F Y W, Z is W.

for_each nil P.
for_each (X::L) P :- P X, for_each L P.
