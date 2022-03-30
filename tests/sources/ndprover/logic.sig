/*
 * Encodings for the basic categories of expressions and the logical 
 * constants in a first order object logic
 */

sig logic.

kind    i       type.
kind    bool    type.

type    (&&)     bool -> bool -> bool.
type    (||)      bool -> bool -> bool.
type    (==>)     bool -> bool -> bool.
type    neg     bool -> bool.
type    forall  (i -> bool) -> bool.
type	some    (i -> bool) -> bool.
type    perp    bool.
