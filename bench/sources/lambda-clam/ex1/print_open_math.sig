/* 

File: print_open_math.sig
Author: Louise Dennis / Jurgen Zimmer / James Brotherston
Description: Pretty printing for OpenMath terms
Last Modified: 14th August 2002

*/

sig print_open_math.

accum_sig print_syntax.

type print_open_math  osyn -> string -> o.
type print_open_math_ osyn -> string -> o.	

type open_math_show_goal goal -> o.
type open_math_show_hyp  osyn -> o.
	
type zero         osyn.
type one          osyn.
type triv_var     osyn -> o.

end
