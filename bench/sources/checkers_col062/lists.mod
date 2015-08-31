% 29 july 2014.
module lists.

type rev list A -> list A -> list A -> o.


member X [X|_].
member X [Y|R] :- member X R.

normalize G :- term_to_string G S, G.


append nil K K.
append (X::L) K (X::M) :- append L K M.

foreach P nil.
foreach P (X::L) :- P X, foreach P L.

forsome P (X::L) :- P X; forsome P L.

memb_and_rest X (X::L) L.
memb_and_rest X (Y::K) (Y::L) :- memb_and_rest X K L.

reverse L K :- rev L nil K.
rev nil L L.
rev (X::L) K M :- rev L (X::K) M.

foldl P nil X X.
foldl P (Z::L) X Y :- P Z X W, foldl P L W Y.

length [] 0.
length (X::Q) N :- length Q N', N is N' + 1.
