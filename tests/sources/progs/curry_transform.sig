/*
 * Interface to code for transforming a function that takes a pair as 
 * argument into an equivalent one that takes two separate arguments
 */

sig  curry_transform.

accum_sig  fp_vocab, fp_types.

exportdef  curry  tm -> tm -> o.
