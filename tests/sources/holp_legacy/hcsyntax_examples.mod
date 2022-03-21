/*
 * A testing harness for code that analyzes the structure of formula
 * representation; the particular analysis involves recognizing 
 * goals and program clauses in Horn clause logic
 */

module  hcsyntax_examples.

accumulate  hc_syntax, refl_syntax.

/* some sample formulas */
formula  1  (some x \ ((path a x) and (path x b))).
formula  2  (some x \ ((path a x) imp (path x b))).
formula  3  ((path a b) and (path b a)).
formula  4  ((path a b) imp (path b a)).

formula  5  ((path a b) imp (adj a b)).
formula  6  (all x\ all y\ ((path x y) imp (adj x y))).
formula  7  (all x\ all y\ (((path x y) imp (adj x y)) imp (adj x y))).

/* testing whether or not one of the formulas above is a goal or a clause */
test_goal N :- formula N F, goal F. 
test_defcl N :- formula N F, def_clause F.
