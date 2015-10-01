/*

File: pds_support.sig
Author: Louise Dennis / James Brotherston
Description: Persistant Data Structure Planner (with Critics).
Last Modified: 16th August 2002

*/

sig pds_support.

%% Accumulate pretty-printing code with lclam syntax and planner switches

accum_sig pretty_printer, switch.


%% Declarations carried over from plan_support

type cpstate agenda -> cplan -> plan_state.

type create_agenda action -> plan_state -> (action -> plan_state -> plan_state -> o) -> plan_state -> switch -> o.

type depth_first_plan action -> plan_state -> plan_state -> o.


%% Signature for this module

type pds_method_trans goal -> meth -> meth -> meth -> o.

type context_plan_step action -> action -> agenda -> agenda -> (list changed_node) -> switch -> int -> o.

type build_plan (list int) -> cplan -> o.

type -1 int.  %% declare -1 as int for use as a null depth limit

%% method scoring clauses for treating the best-first methodical

type score_method  goal -> meth -> int -> o.

end