/*

File: plan_support.sig
Author: Louise Dennis / James Brotherston
Description: Persistant Data Structure Planner (with Critics).
Last Modified: 16th August 2002

*/

sig plan_support.

% By importing pretty_printer we also get lclam_syntax

accum_sig pretty_printer, switch.

type cpstate agenda -> cplan -> plan_state.

type tidy_continuation meth -> meth -> o.

type apply_method_to_goal action -> meth -> goal -> goal -> (list preconditions) -> o.
type expand_compound_method meth -> meth -> o -> (list int) -> o.

type create_agenda action -> plan_state -> (action -> plan_state -> plan_state -> o) -> plan_state -> switch -> o.

type depth_first_plan action -> plan_state -> plan_state -> o.


end
