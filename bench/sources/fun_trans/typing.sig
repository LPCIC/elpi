sig typing.

accum_sig terms.
accum_sig types.

% [infer_tp +T ?TP] tries to infer type [TP] of term [T]. May loop,
% because type inference algorithm not complete (polymorphic typing)!
type infer_tp tm -> tp -> o.
