% Where does the zebra live?
% Puzzle solution written by Claude Sammut.

module zebra.

iter0 zero X.
iter0 (s N) X :- X, iter0 N X.

plus0 zero X X.
plus0 (s X) Y (s S) :- plus0 X Y S.

mult0 zero X zero.
mult0 (s X) Y Z :- mult0 X Y K, plus0 Y K Z.

exp0 zero X (s zero).
exp0 (s X) Y Z :- exp0 X Y K, mult0 Y K Z.

main :-
 TEN = s (s (s (s (s (s (s (s (s (s zero))))))))),
 mult0 TEN TEN HUNDR,
 iter0 HUNDR once.


once :-
	houses Houses,
	member (house red english Dummy1 Dummy2 Dummy3) Houses,
	member (house Dummy4 spanish dog Dummy5 Dummy6) Houses,
	member (house green Dummy10 Dummy11 coffee Dummy12) Houses,
	member (house Dummy13 ukrainian Dummy14 tea Dummy15) Houses,
	right_of (house green Dummy16 Dummy17 Dummy18 Dummy19) (house ivory Dummy20 Dummy21 Dummy22 Dummy23) Houses,
	member (house Dummy24 Dummy25 snails Dummy26 winstons) Houses,
	member (house yellow Dummy27 Dummy28 Dummy29 kools) Houses,
	Houses = (xcons Dummy30 (xcons Dummy31 (xcons (house Dummy32 Dummy33 Dummy34 milk Dummy35) (xcons Dummy36 (xcons Dummy37 xnil))))),
	Houses = (xcons (house Dummy38 norwegian Dummy39 Dummy40 Dummy41) Dummy42),
	next_to (house Dummy43 Dummy44 Dummy45 Dummy46 chesterfields) (house Dummy47 Dummy48 fox Dummy49 Dummy50) Houses,
	next_to (house Dummy51 Dummy52 Dummy53 Dummy54 kools) (house Dummy55 Dummy56 horse Dummy57 Dummy58) Houses,
	member (house Dummy59 Dummy60 Dummy61 orange_juice lucky_strikes) Houses,
	member (house Dummy62 japanese Dummy63 Dummy64 parliaments) Houses,
	next_to (house Dummy65 norwegian Dummy66 Dummy67 Dummy68) (house blue Dummy69 Dummy70 Dummy71 Dummy72) Houses,
	member (house Dummy73 Dummy74 zebra Dummy75 Dummy76) Houses,
	member (house Dummy77 Dummy78 Dummy79 water Dummy80) Houses,
	print_houses Houses.

houses (xcons (house Dummy16 Dummy17 Dummy18 Dummy19 Dummy20) (xcons 
	(house Dummy116 Dummy117 Dummy118 Dummy119 Dummy120) (xcons 
   (house Dummy216 Dummy217 Dummy218 Dummy219 Dummy220) (xcons 
   (house Dummy316 Dummy317 Dummy318 Dummy319 Dummy320) (xcons 
   (house Dummy416 Dummy417 Dummy418 Dummy419 Dummy420) xnil))))).

right_of A B (xcons B (xcons A Dummy)).
right_of A B (xcons Dummy Y) :- right_of A B Y.

next_to A B (xcons A (xcons B Dummy)).
next_to A B (xcons B (xcons A Dummy)).
next_to A B (xcons Dummy Y) :- next_to A B Y.

member X (xcons X Dummy).
member X (xcons Dummy Y) :- member X Y.

print_houses (xcons A B) :- !,
%	write(A), nl,
%   $print A,
	print_houses B.
print_houses xnil.
