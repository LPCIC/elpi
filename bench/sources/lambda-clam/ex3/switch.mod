/*

File: switch.mod
Author: Louise Dennis / James Brotherston
Description: Support for Top Level Loops
Last Modified: 16th August 2002

*/

module switch.

step_by_step_m off.
step_by_step_mode S:-
	step_by_step_m T, !,
	T = S.

spypoint_m off _.
spypoint_mode S Meth:-
	spypoint_m T Meth, !,
	T = S.

end