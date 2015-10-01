/* 

File: print_open_math.mod
Author: Louise Dennis / Jurgen Zimmer / James Brotherston
Description: Pretty printing for OpenMath terms
Last Modified: 14th August 2002

*/

module print_open_math.

local string_list_to_string (list string) -> string -> o.

triv_var A :-
	not (not (A = zero)),not (not (A = one)),
        print "triv_var:",
        pprint_term A.

print_open_math X String:-
	print_open_math_ X String, !.

print_open_math (app A (tuple List)) String:- !,
	print_open_math A AString,
	mappred List print_open_math BStringList,
	string_list_to_string BStringList BString,
	String is ("'OMA'(" ^ AString) ^  "[" ^ BString ^ "])".	

print_open_math (app A B) String:- !,
	print_open_math A AString,
	print_open_math B BString,
	String is "'OMA'(" ^ AString ^ "[" ^ BString ^ "])".

print_open_math (abs x\ (P x)) String:- !,
	pi x\ (print_open_math (P x) PString,
		print_open_math x XString),
	String is "'OMBIND'('OMS'(name:\"lambda\" cd:\"fns1\") [" ^ XString ^ "] " ^ PString ^ ")".

print_open_math X String:-
        triv_var X,
        pprint_string "var:",
	pprint_term X,
	has_otype _ X _, !,
	term_to_string X XString,
	String is "'OMV'(name:\"" ^ XString ^ "\")".

print_open_math X String:-
        not (triv_var X),
        pprint_string "non var:",
	pprint_term X,
        has_otype _ X _, !,
	term_to_string X XString,
	String is "'OMS'(name:\"" ^ XString ^ "\" cd:\"arith1\")".

print_open_math (_ arrow _) " ".
print_open_math (tuple_type _) " ".

print_open_math X " ":-
	is_otype _ X _ _.

print_open_math X String:-
	term_to_string X XString,
	String is "'OMV'(name: \"" ^ XString ^ "\")".
	
string_list_to_string nil " ".
string_list_to_string (H::T) StringOut:-
	string_list_to_string T String,
	StringOut is H ^ " " ^ String.

open_math_show_goal (seqGoal (Hyps >>> Conc)):- !,
	for_each Hyps open_math_show_hyp,
	print "|-", print "\n",
	print_open_math Conc PConc,
	print PConc.
	
open_math_show_hyp H:- print_open_math H S, print S, print "\n".
	

end

