/* 
 * Interface to code for inferring monotypes for programs
 * in the simple functional programming language
 */

sig  monoinfer.

accum_sig  pcf, monotypes.

type  infer  tm -> ty -> o.
