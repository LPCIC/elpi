/*
 * Interface to code for recognizing tail recursiveness of arbitrary 
 * arity functions
 */

sig  tailrec.

accum_sig  pcf.

type  term  tm -> o.

exportdef  tailrec  tm -> o.

