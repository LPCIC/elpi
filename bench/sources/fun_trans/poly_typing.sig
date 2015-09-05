sig poly_typing.

accum_sig typing.
accum_sig poly_terms.

% POLYMORPHIC TYPE CHECKING 

% [subsumes +S1 +S2] checks whether type schema [S1] is subsumed by [S2].
type subsumes schema -> schema -> o.

% [generalize +S +T] checks whether the type of term [T] can be
% generalized to type schema [S].
type generalize schema -> tm -> o.

% [instantiate +S +TP] checks whether the type schema [S] can be
% instantiated to type [TP].
type instantiate schema -> tp -> o.
