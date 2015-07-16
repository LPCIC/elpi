/*
 * Recognizing tail recursive functions of arbitrary arguments. 
 * This code illustrates the use of Lambda Prolog scoping devices in
 * realizing recursion over binding structure
 */

module  tailrec.

accumulate refl_syntax.

type  tailrec  tm -> o.
type  trfn     tm -> o.
type  headrec  tm -> o.
type  trbody   tm -> o.

tailrec (fixpt M) :- !, pi F\ ((headrec F) => (trfn (M F))).
tailrec M.

trfn (fn R) :- pi X\ ((term X) => (trfn (R X))).
trfn R :- trbody R.

trbody (cond M N P) :- term M, trbody N, trbody P.
trbody (M @ N) :- !, trbody M, term N.
trbody M :- headrec M; term M.

