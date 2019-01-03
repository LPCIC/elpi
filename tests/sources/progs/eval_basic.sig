/*
 * Signature for a (barebones) call-by-value evaluator for the lambda 
 * calculus
 */

sig  eval_basic.

accum_sig  fp_types.

type   eval  tm -> tm -> o.
