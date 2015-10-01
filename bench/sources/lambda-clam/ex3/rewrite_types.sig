/*

File: rewrite_types.sig
Author: Louise Dennis / James Brotherston
Description: Predicates for rewriting - to be used in theories.
Last Modified: 13th August 2002.

*/

sig rewrite_types.

accum_sig basic_types.

kind polarity       type.
kind rewrite_rule   type.
kind direction	    type.

type user_rewrite string -> rewrite_rule.

/* Predicates whose clauses are defined in other theories */

type definition theory -> rewrite_rule -> osyn -> osyn -> osyn -> o.
type axiom theory -> rewrite_rule -> direction -> osyn -> osyn -> osyn -> o.
type lemma theory -> rewrite_rule -> direction -> osyn -> osyn -> osyn -> o.
type hypothesis theory -> rewrite_rule -> direction -> osyn -> osyn -> osyn -> o.

/* more mnemonic support for polarities stuff */
type ltor direction.
type rtol direction.
type equiv direction.

type negative_polarity polarity.
type positive_polarity polarity.
type equiv_only        polarity.

type polar_term     polarity -> osyn -> osyn. 

type polarise osyn -> osyn -> osyn -> o.

end