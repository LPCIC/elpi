sig let_ext.

accum_sig oper_sem.

% VARIOUS LET-CONSTRUCTORS

% Constructor for arbitrary lifted computations.
type let tm -> (tm -> tm) -> tm.

% Constructor for lifted, possibly non-terminating computations.
type let_mnont tm -> (tm -> tm) -> tm.

% Constructor for lifted expensive computations.
type let_comp tm -> (tm -> tm) -> tm.


% UNSAFE FUNCTIONS

% [unsafe_inline_let +T1 ?T2] inlines the term parameter of
% "let_comp"-terms when it is linear in the function parameter,
% translating it to "let" if it is nonlinear. This assumes that "let_comp"
% and "let_mnont" have been used correctly as, for example, after having
% applied "part_eval" to the term. "let_mnont" is translated to "let"
% always, thus removing all information about termination behaviour.
type unsafe_inline_let tm -> tm -> o.

% [unsafe_let_to_app +T1 ?T2] inlines the term parameter of
% "let_comp"-terms when it is linear in the function parameter,
% translating it to a function application if it is nonlinear. This
% assumes that "let_comp" and "let_mnont" have been used correctly as,
% for example, after having applied "part_eval" to the term. "let_mnont"
% is translated to "let" always, thus removing all information about
% termination behaviour.
type unsafe_let_to_app tm -> tm -> o.
