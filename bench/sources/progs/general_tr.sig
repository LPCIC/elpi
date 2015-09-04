/*
 * Interface to code for recognizing tail recursiveness of arbitrary 
 * arity functions
 */

sig  general_tr.

accum_sig  fp_types, fp_vocab.

type  term  tm -> o.

exportdef  tailrec  tm -> o.

