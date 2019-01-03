/*
 * Interface to the testing harness for the interpreter for the functional 
 * programming language
 */

sig  eval_examples. 

accum_sig  fp_types, fp_vocab. 

type       eval   tm -> tm -> o.
exportdef  test   int -> tm -> o.
