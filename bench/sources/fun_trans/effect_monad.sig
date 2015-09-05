sig effect_monad.

% EFFECT MONAD

% The effect monad guarantees that computational effects are hidden from
% predicates to which "bind" passes terms: in other terms, these terms
% are guaranteed to be values. The specific implementation here makes
% a distinction between values (do not require computation) possibly
% non-terminating computations and other computations. The reason for
% the latter is that "computations" that cannot be done statically
% (reduced to a value) might induce non-linearity if they are applied
% without restrictions.

kind effM type -> type.  % kind of effect monads


% MONAD REPRESENTATION

type value_effM A -> effM A.
type mnont_effM A -> (A -> effM A) -> effM A.
type comp_effM A -> (A -> effM A) -> effM A.


% MONAD OPERATORS

% [unit_value_effM +T ?M] lifts term [T] to the computation (value of
% monadic type) [M], indicating that [T] is a value.
type unit_value_effM A -> effM A -> o.

% [unit_mnont_effM +T ?M] lifts term [T] to the computation [M],
% indicating that evaluating it may cause non-termination.
type unit_mnont_effM A -> effM A -> o.

% [unit_comp_effM +T ?M] lifts term [T] to the computation [M], indicating
% that it still requires (terminating) computation to become completely
% reduced.
type unit_comp_effM A -> effM A -> o.

% [bind_effM +MA +P ?MB] binds the computation [MA] to predicate [P],
% returning the resulting value of monadic type in [MB].
type bind_effM effM A -> (A -> effM B -> o) -> effM B -> o.


% ADDITIONAL FUNCTIONS

% [show_effM +MA ?A] converts the representation of computation [MA]
% to a value [A] of the type on which the effect monad operates. Has to
% be provided by the user!
type show_effM effM A -> A -> o.

% [lifted_term +V ?T] gets the term [T] that has been lifted out of a
% computation using variable [V] in its place.
type lifted_term A -> A -> o.
