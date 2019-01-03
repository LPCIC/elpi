/*
 * The constants and kinds needed for encoding a simple funtional 
 * programming language
 */

sig  fp_vocab.

accum_sig  fp_types.

% conditional and fixed-point operators
type   cond    tm -> tm -> tm -> tm.
type   fix     (tm -> tm) -> tm.

% encodings for integers that uses the lambdaProlog representation
% for these
type   c       int -> tm.

% encodings for booleans of the object language
type   truth   tm.
type   false   tm.
type   &&      tm -> tm -> tm.

% encodings for arithmetic functions of the object language
type   plus    tm -> tm -> tm.
type   minus   tm -> tm -> tm.
type   times   tm -> tm -> tm.
type   lss     tm -> tm -> tm.
type   eq      tm -> tm -> tm.
type   intp    tm -> tm.

% encodings for pairs of the object language
type   pr      tm -> tm -> tm.
type   prp     tm -> tm.
type   fst     tm -> tm.
type   snd     tm -> tm.

% encodings for lists in the object language
type  null  tm.
type  cons  tm -> tm -> tm.
type  hd    tm -> tm.
type  tl    tm -> tm.
type  nullp  tm -> tm.

% encoding of the error value
type   err     tm.


