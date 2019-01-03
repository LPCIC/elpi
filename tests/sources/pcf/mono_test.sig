/*
 * Interface for testing code that infers monomorphic types for
 * programs in the simple functional programming language
 */

sig  mono_test.

accum_sig monoinfer, monotypes.

type  mono_test  string -> ty -> o.
