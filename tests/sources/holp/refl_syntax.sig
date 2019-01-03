/*
 * Interface to code for recognizing some categories of quantifier-free 
 * expressions in a given object logic
 */

sig  refl_syntax.

accum_sig  logic_types, logic_basic, logic_vocab.

/* recognizer for terms */
type  termp        term -> o.

/* Recognizers for atomic and quantifier free formulas; the exportdef 
declaration signifies that the definitions of these predicates is fixed
by this module */
exportdef  atom        form -> o.
exportdef  quant_free  form -> o.





