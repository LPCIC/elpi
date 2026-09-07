########################
Simply-typed λ-calculus
########################

The "hello world" of λ-tree syntax (:doc:`../semantics/logic-programming-model`):
terms and types for the simply-typed λ-calculus, weak-head reduction, and a
type checker that goes under binders with ``pi``/``==>``
(:doc:`../semantics/constraints` extends this very checker to handle
incomplete terms).

.. elpi:: ../code/stlc.elpi
   :assert: type of Fst: arr X0 \(arr X1 X0\)\nwhd \(Fst applied to the identity\): fun c0 \\ fun c1 \\ c1\n\(fun x\\ app x x\) has no type: occur-check failure

Terms are HOAS (:doc:`../syntax/terms-and-operators`): ``app`` pairs a
function with its argument, ``fun`` carries an actual Elpi function
``term -> term`` — so ``λx.λy.x`` is ``fun (x\ fun y\ x)``, and applying that
Elpi function *is* substitution, with no substitution code to write. Types
have one constructor, ``arr``, for the function space.

``whd`` reduces a term to weak-head normal form: unfold ``app`` until the
head is a ``fun``, then β-reduce (apply the Elpi function) and keep going.
Anything else is already in normal form.

``of`` is the type checker. The rule for ``app`` is an ordinary Horn clause;
the rule for ``fun`` needs a fresh name for the bound variable and a rule
that only holds while checking under it — exactly what ``pi``/``==>``
provide (:doc:`../features/hypothetical-rules`,
:doc:`../semantics/logic-programming-model`). Both ``whd`` and ``of`` are
declared ``func`` — each has at most one result — and the determinacy
checker (:doc:`../features/determinacy-checking`) confirms it: ``whd``'s two
overlapping rules are kept apart by the cut, ``of``'s by their distinct head
constructors. Applying a term to itself,
``fun (x\ app x x)``, has no type: to type-check it, ``x``'s type would have
to be a function space with itself as the argument type, and the occur check
(:doc:`../features/unification-and-variables`) rejects the resulting cyclic
assignment.
