/*

File: lclam_utils.mod
Author: James Brotherston
Description: Utility functions for maps, lists etc.
Last Modfied: 13th August 2002

*/

module lclam_utils.

accumulate lclam_map, lclam_list.

local insert_sort (A -> A -> o) -> A -> (list A) -> (list A) -> o.

/*
local quick_sort (A -> A -> o) -> (list A) -> (list A) -> o.
local split (A -> A -> o) -> A -> (list A) -> (list A) -> (list A) -> (list A) -> (list A) -> o.
*/

findall P L:-
	(pi findall_aux\
		((pi L\ pi T\ pi X\
			(findall_aux P L T:-
				P X,
				(not (member X T)), !,
				findall_aux P L (X::T))),
		(pi L\ findall_aux P L L))
			=> (findall_aux P L nil)), !.

%% Actually quicker for the application in mind
insert_sort Measure X nil (X::nil).
insert_sort Measure X (H::T) (H::Out):-
	    Measure H X, !,
	    insert_sort Measure X T Out.
insert_sort Measure X L (X::L).

/*
%% Actually suspect not all that quick because of implementation of append.
quick_sort _ nil nil.
quick_sort Measure (H::T) LSort:-
	   split Mesure H T nil nil L1 L2,
           quick_sort Measure L1 L1Sort,
	   quick_sort Measure L2 L2Sort,
           append L1Sort (H::L2Sort) LSort.

split _ nil _ L1 L2 L1 L2.
split Measure X (H::T) L1in L2in L1out L2out:-
      Measure H X, !,
      split Measure X T (H::L1in) L2in L1out L2out.
split Measure X (H::T) L1in L2in L1out L2out:-
      split Measure X T L1in (H::L2in) L1out L2out.
*/

findall_sort  P L Measure:-
	(pi findall_aux\
		((pi L\ pi T\ pi X\ pi L1\
			(findall_aux P L T:-
				P X,
				(not (member X T)), !,
				insert_sort Measure X T L1,
				findall_aux P L L1)),
		(pi L\ findall_aux P L L))
			=> (findall_aux P L nil)), !.

on_backtracking _.
on_backtracking Commands:-
	Commands, !, fail.

end
