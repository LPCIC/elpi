sig poly_terms.

accum_sig terms.
accum_sig poly_types.

% ADDITIONAL TERMS FOR A SIMPLE FUNCTIONAL LANGUAGE
% THEY ALLOW POLYMORPHIC TYPE CHECKING (MANDATORY TYPE SEMANTICS)

% Type declaration for lambda abstractions.
type tlam tp -> (tm -> tm) -> tm.

% Type declaration for recursive functions (fixed point operator).
type trec tp -> (tm -> tm -> tm) -> tm.

% Type declaration for abstractions with let-polymorphism.
type tlet schema -> tm -> (tm -> tm) -> tm.

% Type abstraction.
type tabs (tp -> tm) -> tm.


% BASIC OPERATIONS ON POLYMORPHIC TERMS

% [tm_of_ptm +T1 ?T2] converts a polymorphic term [T1] to a normal term
% [T2].
type tm_of_ptm tm -> tm -> o.

% [output_ptm +Out +T] prints polymorphic term [T] to output stream [Out].
type output_ptm out_stream -> tm -> o.

% [print_ptm +T] prints polymorphic term [T] to standard output.
type print_ptm tm -> o.
