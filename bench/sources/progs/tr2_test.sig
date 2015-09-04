/* 
 * Interface to code for testing the predicate for recognizing
 * tail recursiveness of arbitrary arity functions
 */

sig  tr2_test.

accum_sig  fp_types, fp_vocab, terms.

kind name type.

exportdef test  int -> o.

exportdef trm name -> tm -> o.

