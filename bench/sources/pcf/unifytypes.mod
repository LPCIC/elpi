/*
 * Code for unifying types. Types are assumed to be represented like
 * monotypes, i.e. without explicit quantification, with one exception:
 * variables are not represented by meta variables but, rather, by 
 * special constants of which the predicate tvar is true.
 */

module unifytypes.

accum_sig   monotypes.

accumulate  control.

type  tvar  ty -> o.

% Representation of disagreement pairs
kind  eq       type.             
type  ==       ty -> ty -> eq.
infix ==       4.


% subst_ty is a predicate such that (subst_ty V T Ty1 Ty2) is true if
% replacing all occurrences of V in type Ty1 by T produces the type
% Ty2; V is assumed to be (a special constant representing) a variable.
type subst_ty   ty -> ty -> ty -> ty -> o.

subst_ty V T Var S  :- tvar Var, if (V = Var) (S = T) (S = Var).
subst_ty V T num num.
subst_ty V T bool bool.
subst_ty V T (lst A) (lst B) :- subst_ty V T A B.
subst_ty V T (A --> B) (Ax --> Bx) :- subst_ty V T A Ax,  subst_ty V T B Bx.


% Transforming an equation through a substitution
type subst_eq   ty -> ty ->      eq ->      eq -> o.

subst_eq  V T (A == B) (Ax == Bx) :- subst_ty V T A Ax, subst_ty V T B Bx.

% Transforming a set of equations through a substitution
type subst_eqs  ty -> ty -> list eq -> list eq -> o.

subst_eqs V T nil nil.
subst_eqs V T (Eq :: Eqs) (Eq' :: Eqs') :- 
    subst_eq V T Eq Eq', subst_eqs V T Eqs Eqs'.

% Checking if (a constant representing) a variable has occurrences 
% in a type
type free_occ  ty -> ty -> o.

free_occ V V         :- tvar V.
free_occ V (A --> B) :- free_occ V A; free_occ V B.
free_occ V (lst A)   :- free_occ V A.


% The main unification predicate; (unify Eqs In Out) is true if solving
% the equations represented by Eqs results in In being instantiated to Out
type  unify       list eq -> ty -> ty -> o.

unify nil In In.
unify ((A == A) :: Eqs) In Out :- !, unify Eqs In Out.
unify ((A --> Ax == B --> Bx) :: Eqs) In Out :-
  unify ((A == B) :: (Ax == Bx) :: Eqs) In Out.
unify ((lst A == lst B) :: Eqs) In Out :- unify ((A == B) :: Eqs) In Out.
unify ((A == B) :: Eqs) In Out &
unify ((B == A) :: Eqs) In Out :- 
  tvar A, !, not (free_occ A B),
  subst_eqs A B Eqs Eqsx,
  subst_ty    A B In  Mid,
  unify Eqsx Mid Out.
