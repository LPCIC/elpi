/* 

File: print_syntax.sig
Author: Louise Dennis / James Brotherston
Description: pretty printing for syntax
Last Modified: 14th August 2002

*/

sig print_syntax.

accum_sig prettify, interaction.

type pprint_term            osyn -> o.
type pprint_name            A -> o.
type pprint_address         A -> B -> o.
type pprint_rewrite_rule    direction -> osyn -> osyn -> osyn -> o.
type pprint_subst           subst -> o.
type pprint_goal            goal -> o.
type xb_pprint_goal         out_stream -> goal -> o.
type pprint_name_list       (list A) -> o.
type pprint_methodical      meth -> o.
type pprint_predicate       o -> o.
type pprint_tactic          tactic -> o.
type pprint_string          string -> o.

type printstdout            A -> o.




end
