/*
 * Representing polytypes. Uses monotypes as the base, reflecting these
 * into the encoding through a special constructor and adding 
 * quantification. No type variables are assumed to appear in types at
 * this level.
 */

sig  polytypes.

accum_sig  monotypes.

kind   poly    type.                

type   all     (ty -> poly) -> poly.
type   c       ty -> poly.




