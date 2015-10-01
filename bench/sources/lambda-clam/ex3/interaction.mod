/*

File: interaction.mod
Author: Louise Dennis / James Brotherston
Description:  Predicates for controlling the various printing modes
Last Modified: 16th August 2002

*/

module interaction.

interactive command_pretty.
interactive_mode S:-
	interactive T, !,
	T = S.

plan_printing_sw off.
plan_printing_switch S:-
	plan_printing_sw T, !,
	T = S.

% default output settings
verbose_m on.
silent_m off.
super_silent_m off.

verbose S:- verbose_m T, !, T = S.

silent S:- silent_m T, !, T = S.

super_silent S:- super_silent_m T, !, T = S.

end
