sig termination.

accum_sig terms.
accum_sig part_eval.

% [converges +T] checks whether term [T] converges, i.e. whether
% evaluating it would terminate. This is generally undecidable, but if
% this predicate succeeds, termination is guaranteed.
type converges tm -> o.
