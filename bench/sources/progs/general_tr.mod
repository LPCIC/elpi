/*
 * Recognizing tail recursive functions of arbitrary arguments. 
 * This code illustrates the use of Lambda Prolog scoping devices in
 * realizing recursion over binding structure
 */

module  general_tr.

accumulate refl_syntax.

type  tailrec  tm -> o.
type  trfn     tm -> o.
type  headrec  tm -> o.
type  trbody   tm -> o.

tailrec (fix M) :- pi F\ ((headrec F) => (trfn (M F))).

trfn (abs R) :- pi X\ ((term X) => (trfn (R X))).
trfn R :- trbody R.

trbody (cond M N P) :- term M, trbody N, trbody P.
trbody M :- term M ; headrec M.

headrec (app M N) :- headrec M, term N.
