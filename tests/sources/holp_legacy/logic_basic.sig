/*
 * This file defines encodings for the logical symbols in a 
 * first-order logic. 
 */

sig  logic_basic.

accum_sig  logic_types.

/* Constants encoding the logical symbols; note the types of the 
generalized quantifiers */
type   perp    form.
type   tru     form.
type   and     form -> form -> form.
type   or      form -> form -> form.
type   imp     form -> form -> form.
type   all     (term -> form) -> form.
type   some    (term -> form) -> form.


/* Some operator declarations for syntactic convenience */
infixr  and   120.
infixr  or    120.
infixr  imp   110.
