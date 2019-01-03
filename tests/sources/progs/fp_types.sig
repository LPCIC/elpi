/*
 * The sorts and constants needed for encoding the terms in the
 * untyped lambda calculus
 */

sig  fp_types.

kind  tm type.

type   abs   (tm -> tm) -> tm.
type   app   tm -> tm -> tm.

