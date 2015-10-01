/*

File: planner.sig
Author: Louise Dennis / James Brotherston
Description: Persistant Data Structure Planner (with Critics).
Last Modified: 16th August 2002

*/

sig planner.

%% We extend the signature of the planner core with that of the pretty-printer
%% and of the sockets module

accum_sig pretty_printer, sockets.

%% Planner wrappers

type pds_plan          meth -> query -> o.
type pds_iter_plan     meth -> query -> o.
type claudio_plan      meth -> query -> cplan -> o.
type claudio_iter_plan meth -> query -> cplan -> o.

%% Various planners (although I think these should be removed to enforce 
%% the use of wrappers -JB)

type plan_this (plan_state -> (action -> plan_state -> plan_state -> o) -> plan_state -> o) -> meth -> query -> (action -> plan_state -> plan_state -> o) -> plan_state -> o.
type part_planner plan_state -> (action -> plan_state -> plan_state -> o) -> plan_state -> o.
type pds_planner plan_state -> (action -> plan_state -> plan_state -> o) -> plan_state -> o.
type depth_first_plan action -> plan_state -> plan_state -> o.

%% Support for planner switches

type step_by_step_mode switch -> o.
type step_by_step_m    switch -> o.

type spypoint_m       switch -> meth -> o.
type spypoint_mode    switch -> meth -> o.

%% Support for heuristic scoring of methods

type score_method  goal -> meth -> int -> o.

end
