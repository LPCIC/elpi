/*
 * Interface to a recognizer of valid program terms
 */

sig  refl_syntax. 

accum_sig  fp_types, fp_vocab. 

/* the definition of this predicate may need to be dynamically extended */
type   term      tm -> o.
