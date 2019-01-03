/*
 * Interface to code for unifying types. Types are assumed to be 
 * represented like monotypes, i.e. without explicit quantification, 
 * with one exception: variables are not represented by meta variables 
 * but, rather, by special constants of which the predicate tvar is true.
 */

sig  unifytypes.

accum_sig  monotypes.

% predicate for encoding type variables
type  tvar  ty -> o.

% Representation of disagreement pairs
kind  eq       type.             
type  ==       ty -> ty -> eq.
infix ==       4.

% (unify Eqs In Out) is true if solving the equations represented by 
% Eqs results in In being instantiated to Out 
type  unify       list eq -> ty -> ty -> o.

