/*
 * Interface to the call-by-value interpreter for PCF
 */

sig eval.

accum_sig  pcf.

%type special       tm -> int -> list tm -> tm.

type eval          tm -> tm -> o.
