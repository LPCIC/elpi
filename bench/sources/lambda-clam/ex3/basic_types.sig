/*

File: basic_types.sig
Author: James Brotherston
Description: Type declarations for fundamental proof planner elements
Last Modified: 13th August 2002

*/

sig basic_types.

kind  osyn     type.
kind  theory   type.
kind  goal     type.
kind  query    type.
kind  meth     type.
kind  tactic   type.
kind  crit     type.



%% This should really be elsewhere - maybe we should collect all the  
%% user-defined entity wrappers in one place JB

type  user_theory string -> theory.




end