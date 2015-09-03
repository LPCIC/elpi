/*
 * A harness for testing the transformation of formulas to prenex
 * normal form
 */

module  pnf_examples. 

accumulate  refl_syntax, pnf.

type  formula  int -> form -> o.

formula 1  ((all (X \ (path a X))) imp tru).
formula 2  ((some (X \ (path a X))) imp tru).
formula 3  ((all (X \ (path a X))) and (all (Y \ (path Y a)))).
formula 4  ((some (X \ (path a X))) imp ((all (Y \ (path a Y))))).

(test N F) :- (formula N OF), (prenex OF F).

