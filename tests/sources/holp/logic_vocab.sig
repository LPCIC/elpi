/* 
 * This file defines encodings for the nonlogical symbols in a
 * first-order logic
 */

sig  logic_vocab.

accum_sig  logic_types.

/* The constants and function symbols */
type   a      term.
type   b      term.
type   c      term.
type   f      term -> term.

/* The predicate symbols */
type   path   term -> term -> form.
type   adj    term -> term -> form.

