/* 

File: pretty_printer.sig
Author: James Brotherston
Description: Interface to the pretty printer
Last Modified: 15th August 2002

*/

sig pretty_printer.

%% import LClam syntax declarations and interaction modes

accum_sig lclam_syntax, interaction.

%% Support for theory-specific pretty printing clauses

kind  thing   type. 

type prettify_term             osyn -> thing -> o.
type prettify_special          osyn -> thing -> o.
type pretty_show_term          osyn -> o.
type pretty_show_goal          goal -> o.
type pretty_show_goal_special  goal -> o.

type  blo     int -> list thing -> thing.
type  str     string -> thing.
type  abstr   int -> (A -> list thing)  -> thing.
type  brk     int -> thing.
type  pr      out_stream -> thing -> int -> o.                     
type  lvar    (A -> thing).  

%% Syntax pretty printing

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

%% Plan pretty printing

kind cplan type.

type eplan cplan.
type c_and_node goal -> (list int) -> meth -> (list cplan) -> cplan.
type c_forall_node (list int) -> (A -> cplan) -> cplan.
type c_exists_node (list int) -> (A -> cplan) -> cplan.

type xbmode in_stream -> out_stream -> o.

type pprint_plan plan -> o.
type pprint_cplan cplan -> o.

%% OpenMath pretty printing

type print_open_math  osyn -> string -> o.
type print_open_math_ osyn -> string -> o.	

type open_math_show_goal goal -> o.
type open_math_show_hyp  osyn -> o.
	
type zero         osyn.
type one          osyn.
type triv_var     osyn -> o.

%% Miscellaneous planner output

type plan_step_prompts     (list changed_node) -> o -> o.
type pprint_method_failure meth -> goal -> (list int) -> o.
type pprint_method_success meth -> goal -> (list int) -> o.

%% Printing clauses which depend on output mode

type maybe_pprint_goal            goal -> o.
type maybe_pprint_method_attempt  meth -> goal -> (list int) -> o.
type maybe_pprint_backtracking    meth -> goal -> o.

end