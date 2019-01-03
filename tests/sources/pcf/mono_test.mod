/* 
 * A testing harness for code that infers monotypes for programs in
 * the simple functional programming language
 */

module mono_test.

accumulate monoinfer, examples.

type mono_test   string -> ty -> o.

mono_test String Type :- prog String Term, infer Term Type.
