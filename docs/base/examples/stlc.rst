########################
Simply-typed λ-calculus
########################

The "hello world": terms and types for the simply-typed λ-calculus,
weak-head reduction, and a type checker that goes under binders with
``pi``/``==>`` and suspends on the holes of an incomplete term rather than
guessing what they stand for.

:doc:`../semantics/constraints` picks the checker up from here: why matching
rather than unifying is what lets it suspend, and how a constraint handling
rule then rejects the holes that admit no consistent type.

.. elpi:: ../code/stlc.elpi
   :assert: type of Fst: arr X\d+ \(arr X\d+ X\d+\)\nwhd \(Fst applied to the identity\): fun c\d+ \\ fun c\d+ \\ c\d+\n\(fun x\\ app x x\) has no type: occur-check failure\nof \(app H _\): H unknown, so of suspends:\n of X\d+ X\d+  /\* suspended on X\d+ \*/ of X\d+ \(arr X\d+ X\d+\)  /\* suspended on X\d+ \*/\nafter H := the identity, its constraint resumed:\n of X\d+ X\d+  /\* suspended on X\d+ \*/

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
declared ``func`` — each has at most one result — and the determinacy checker
(:doc:`../features/determinacy-checking`) confirms it: ``whd``'s two
overlapping rules are kept apart by the cut, ``of``'s three by their distinct
heads.

Applying a term to itself, ``fun (x\ app x x)``, has no type: to type-check
it, ``x``'s type would have to be a function space with itself as the
argument type, and the occur check
(:doc:`../features/unification-and-variables`) rejects the resulting cyclic
assignment.

The last rule of ``of`` is what makes the checker usable on a term that is
still being built. ``of (uvar as Hole) T`` matches a bare unification
variable — a hole — and instead of failing (no term to inspect) or looping
(if the argument were unified rather than matched,
:doc:`../semantics/logic-programming-model`), it suspends: ``of Hole T``
becomes a constraint, keyed on ``Hole``, to be retried once ``Hole`` is
known. So ``of (app H _) _`` with ``H`` unknown succeeds, leaving two
suspended ``of`` goals in the store; assigning ``H`` the identity wakes its
constraint, which resolves and leaves just the one still waiting on the
argument.
