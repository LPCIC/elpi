/* 

File: print_plan.sig
Author: Louise Dennis / James Brotherston
Description: Pretty printing for plans
Last Modified: 14th August 2002

*/

sig print_plan.

accum_sig print_syntax.

kind plan type.
kind cplan type.

type eplan cplan.
type c_and_node goal -> (list int) -> meth -> (list cplan) -> cplan.
type c_forall_node (list int) -> (A -> cplan) -> cplan.
type c_exists_node (list int) -> (A -> cplan) -> cplan.

type xbmode in_stream -> out_stream -> o.

type pprint_plan plan -> o.
type pprint_cplan cplan -> o.



end