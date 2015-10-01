/*

File: switch.sig
Author: Louise Dennis / James Brotherston
Description: Various planner switches
Last Modified: 16th August 2002

*/

sig switch.

kind switch type.
kind meth   type.

type on  switch.
type off switch.

type step_by_step_mode switch -> o.
type step_by_step_m    switch -> o.

type spypoint_m       switch -> meth -> o.
type spypoint_mode    switch -> meth -> o.




end
