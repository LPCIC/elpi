/*
 * Encodings for the basic categories of expressions and the logical 
 * constants in a first order object logic
 */

sig logic.

kind    i       type.
kind    bool    type.

type    and     bool -> bool -> bool.
type    or      bool -> bool -> bool.
type    imp     bool -> bool -> bool.
type    neg     bool -> bool.
type    forall  (i -> bool) -> bool.
type	some    (i -> bool) -> bool.
type    perp    bool.

infixr  and 140.
infixr  or  140.
infixr  imp 130.
