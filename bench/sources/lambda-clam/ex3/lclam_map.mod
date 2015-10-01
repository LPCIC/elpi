/*

File: lclam_map.mod
Author: Louise Dennis / James Brotherston
Description: Map utility functions
Last Modified: 13th August 2002

*/

module lclam_map.

mapfun nil F nil.
mapfun [X|L] F [(F X)|K] :- mapfun L F K.

mappred nil P nil.
mappred (X::L) P (Y::K) :- 	 
 P X Y, mappred L P K.

for_each nil P.
for_each (X::L) P :- P X, for_each L P.

for_each_cut nil P.
for_each_cut (X::L) P :- 
			 P X, 
                         !, 
			 for_each_cut L P.

for_one nil _ _ :- !, fail.
for_one (H::_) F H :- F H.
for_one (_::T) F Success:- for_one T F Success.

/*
map_app L1 P L2:- map_app2 L1 _ (H1\ H2\ H3\ (P H1 H3)) L2.

map_app2 nil nil _ nil.
map_app2 (H1::T1) (H2::T2) F Out :-
	F H1 H2 L, !,
	map_app2 T1 T2 F Tl,
	append L T1 Out.
*/

forthose nil P nil nil :- !.
forthose (X::L) P (Y::K) (W::Z):- P X Y W, !, forthose L P K Z.
forthose L P (Y::K) Z:- forthose L P K Z, !.

/*
forthose2 nil P nil nil nil nil nil:- !.
forthose2 (X::L) P (Y::K) (W::Z) (X::Out) (A::AT) (A::BT):- P X Y W, !, forthose2 L P K Z Out AT BT.
forthose2 (X::L) P (Y::K) Z Out (_::AT) BT:- forthose2 L P K Z Out AT BT, !.
*/

mappred2 nil _ nil nil.
mappred2 (H::T) P (H1::T1) (H2::T2):-
	P H H1 H2, !,
	mappred2 T P T1 T2.

mapcount nil _ nil nil _:- !.
mapcount (H::T) P (H1::T1) (H2::T2) Counter:-
	P H H1 H2 Counter, !, 
	C is Counter + 1,
	mapcount T P T1 T2 C, !.

/*
filter L1 P L2:- filter2 L1 _ L2 _ _ (H1\ H2\ H3\ (P H1 H3)).
*/

filter2 nil _ nil nil nil _:- !.
filter2 _ nil nil nil nil _:- !.
filter2 (H1::T1) (H2::T2) (H3::T3) (H4::T4) (H4::T5) F:- F H1 H2 H3, !,
	filter2 T1 T2 T3 T4 T5 F.
filter2 (_::T1) (_::T2) T3 (_::T4) T5 F :- filter2 T1 T2 T3 T4 T5 F.

/*
mapbuild F (H::nil) H.
mapbuild F (H::T) (F H Out):-
	mapbuild F T Out.
*/

end
