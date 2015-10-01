/*

File: lclam_list.mod
Author: Louise Dennis / James Brotherston
Description:  List utility functions
Last Modified: 13th August 2002

*/

module lclam_list.

memb X (X::L).
memb X (Y::L) :- memb X L.

member X (X::L) :- !.
member X (Y::L) :- member X L.

append nil K K.
append (X::L) K (X::M) :- append L K M.

length nil 0.
length (_::T) N :-
	length T N1,
	N is N1 + 1.

nth (H::T) 1 H T.
nth _ 0 _ _ :- fail.
nth (H::T) N El (H::Residue):-
	(not (N = 0)), !,
	N1 is N - 1,
	nth T N1 El Residue.
nth L N El (H::Residue):-
	(not (L = nil)), 
	!,
	(L = (H::T)),
	nth T N1 El Residue,
	N is N1 + 1.
nth nil _ _ _ :- fail.

memb_and_rest A (A::Rest) Rest.
memb_and_rest A (B::Tail) (B::Rest) :-
	memb_and_rest A Tail Rest.

drop_l 0 L L:-!.
drop_l N (_H::T) Out:-
	N1 is (N - 1), !,
	drop_l N1 T Out.

reverse L1 L2 :-
   (pi rev_aux \
      ((rev_aux nil L2,
        (pi X\ pi L1\ pi L2\ (rev_aux (X::L1) L2 :- rev_aux L1 (X::L2))))
          => (rev_aux L1 nil))).

end
