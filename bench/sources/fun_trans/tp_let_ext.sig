sig tp_let_ext.

accum_sig tp_terms.

% VARIOUS LET-CONSTRUCTORS

% Constructor for arbitrary lifted computations (typed).
type tp_let tp_astK -> (tp_astK -> tp_astK) -> tp_tm.

% Constructor for lifted, possibly non-terminating computations (typed).
type tp_let_mnont tp_astK -> (tp_astK -> tp_astK) -> tp_tm.

% Constructor for lifted expensive computations (typed).
type tp_let_comp tp_astK -> (tp_astK -> tp_astK) -> tp_tm.


% UNSAFE FUNCTIONS

% [unsafe_tp_inline_let +T1 ?T2] inlines the term parameter of
% "tp_let_comp"-terms when it is linear in the function parameter,
% translating it to "tp_let" if it is nonlinear. This assumes that
% "tp_let_comp" and "tp_let_mnont" have been used correctly as, for
% example, after having applied "tp_part_eval" to the term. "tp_let_mnont"
% is translated to "tp_let" always, thus removing all information about
% termination behaviour.
type unsafe_inline_tp_let tp_astK -> tp_astK -> o.

% [unsafe_tp_let_to_app +T1 ?T2] inlines the term parameter of
% "tp_let_comp"-terms when it is linear in the function parameter,
% translating it to a function application if it is nonlinear. This
% assumes that "tp_let_comp" and "tp_let_mnont" have been used
% correctly as, for example, after having applied "tp_part_eval" to the
% term. "tp_let_mnont" is translated to "tp_let" always, thus removing
% all information about termination behaviour.
type unsafe_tp_let_to_app tp_astK -> tp_astK -> o.
