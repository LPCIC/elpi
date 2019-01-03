/*
 * Predicates for recognizing some categories of quantifier-free expressions
 * in a given object logic
 */
 
module  refl_syntax.

accum_sig  logic_types, logic_basic, logic_vocab.

type  termp        term -> o.
type  atom         form -> o.
type  quant_free   form -> o.

/* recognizer for terms */
termp a.
termp b.
termp c.
termp (f X) :- termp X.

/* recognizer for atomic formulas */
atom (path X Y) :- termp X, termp Y.
atom (adj X Y) :- termp X, termp Y.

/* recognizer for quantifier free formulas */
quant_free perp.
quant_free tru.
quant_free A :- atom A.
quant_free (B and C) :- quant_free B, quant_free C.
quant_free (B or C) :- quant_free B, quant_free C.
quant_free (B imp C) :- quant_free B, quant_free C.

