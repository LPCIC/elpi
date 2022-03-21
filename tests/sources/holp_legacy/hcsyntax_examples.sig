/*
 * Interface to a testing harness for code that checks if formulas satisfy
 * the structure of goals or program clauses in Horn clause logic
 */

sig  hcsyntax_examples. 

accum_sig  logic_types, logic_basic, logic_vocab.

type formula int -> form -> o.

type  test_goal, test_defcl  int -> o.



