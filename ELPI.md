# Extensions to λProlog implemented in ELPI

- [Underscore](#underscore) is a real wildcard

- [Macros](#macros) are expanded at compilation time

- [Spilling](#spilling) turns `..{foo X}..` into `foo X Y,..Y..`

- [N-ary binders](#n-ary-binders) let one write `pi x y z\ ...`

- [N-ary implication](#n-ary-implication) let one write `[p,q] => g`

- [Non logical features](#non-logical-features) like `!` or `new_safe`

- [Typechecking](#typechecking) is performed by `elpi-checker.elpi`
  on the quoted syntax of the program and query

- [Subterm naming](#subterm-naming) can be performed
  using an `as X` annotation

- [Clause grafting](#clause-grafting) can inject a clause
  in the middle of an existing program

- [Modes](#modes) can be declared in order to control the generative
  semantics of Prolog

- [Syntactic constraints](#syntactic-constraints) are goals suspended on
  a set of variables that are resumed when any of them gets assigned and
  that can be manipulated by CHR like rules

- [Quotations](#quotations) let you write terms in a custom syntax and
   have ELPI translate them into λProlog terms.  This is only available
   via the OCaml API.

- [Namespaces](#namespaces) are to avoid name conflicts. This is a very
  simple syntactic facility to add a prefix to all names declared in a
  specific region.

- [Advanced modes](#advanced-modes) can be used to declare the same code
  with different modes under different names.

- [Accumulate with paths](#accumulate-with-paths) accepts `accumulate "path".`
  so that one can use `.` in a file/path name.
  
## Underscore

Identifiers whose name start with `_` are wildcards, not variables.

```prolog
trivial-facts :-
  _ = whatever,
  you-name-it = _Whatever,
  pi x\ _ = x.
% pi x\ _ x = x. -- invalid syntax, _ is not a variable
```

Side note: no solution is computed for goals like `_ = something`.
On the contrary a problem like `DummyNameUsedOnlyOnce = somthing` demands the
computation of the solution (even if it is not used), and hence can *fail* if
some variable occurring in something is out of scope for `DummyNameUsedOnlyOnce`.

Side note: `elpi-checker.elpi` (see below) reports warnings about linearly used
variables, suggesting to start their name name not starting with `_`.

## Macros

A macro is declared with the following syntax
```prolog
macro @name Args :- Body.
```
It is expanded everywhere (even in type declarations)
at compilation time.

#### Example: type shortcut.
```prolog
macro @context :- list (pair string term).
type typecheck @context -> term -> term -> prop.
```

#### Example: logging.
```prolog
macro @log P :- (P :- debug-print "goal=" P, fail).

% @log (of _ _). % uncomment to trace of
of (lambda N F) :- ...
of (app H A) :- ...
```

#### Example: factor hypothetical clauses.
```prolog
macro @of X N T :- (of X T, pp X N).
of (lambda Name   F) (arr A B) :-         pi x\ @of x Name A =>            of (F x) B.
of (let-in Name V F) R         :- of V T, pi x\ @of x Name T => val x V => of (F x) R.
```

#### Example: optional cut.
```prolog
macro @neck-cut-if P Hd Hyps :- (
  (Hd :- P,      !, Hyps),
  (Hd :- not P,     Hyps)
).

@neck-cut-if greedy 
(f X)  (X = 1).
 f X :- X = 2.
```

```
goal> greedy => f X.
Success:
  X = 1
goal> f X.
Success:
  X = 1
More? (Y/n)
Success:
  X = 2 
```
## Spilling
The following boring code
```prolog
f X R :- foo X Y, bar Y R.
```
can be written as
```prolog
f X R :- bar {foo X} R.
```
since ELPI rewrites the latter program into 
```prolog
f X R :- foo X Spilled_1, bar Spilled_1 R.
```

For spilling to work, ELPI has to know the arity of the spilled predicate.
Both a `type` or `mode` declaration suffice.
```prolog
type f int -> int -> int -> prop
type g int -> int -> prop
main :- g {f 3}.
```

Spilling under `pi` is supported
```prolog
foo :- pi x\ f {g x}
```
rewrites to
```prolog
foo :- pi x\ sigma Spilled_1\ g x Spilled_1, f Spilled_1.
```
so that `Spilled_1` sees `x` and can receive the "result" of `g`.

Spilling under a lambda is supported.
```prolog
foo R :- R = lam x\ g {mk-app f [x,g x]}.
```
rewrites to
```prolog
foo R :- (pi x\ mk-app f [x,g x] (Spilled_1 x)), R = lam x\ g (Spilled_1 x).
```

### Caveat about spilling
The spilled predicate invocation is inserted just before the closest
predicate invocation.  Currently "what is a predicate" takes into account
only monomorphic, first order, type declarations. E.g. of badly supported
spilling
```prolog
foo L L1 :- map L (x\y\ f {g x} y) L1.
```
rewrite to (the probably unwanted)
```prolog
foo L L1 :- (pi x\ pi y\ g x (Spilled_1 x y)), map L (x\y\ f (Spilled_1 x y) y) L1.
```
whenever the type of `f` (applied to two arguments) is not known
to be `prop` (i.e. no type is declared for `f`, even if the type of
`map` is known and imposes `f _ _` to be of type `prop`). With a type
declaration as
```prolog
type f term -> term -> prop.
```
the rewritten clause is the expected
```prolog
foo L L1 :- map L (x\y\ sigma Spilled_1\ g x Spilled_1, f Spilled_1 y) L1.
```
since the closest predicate before the spilling is, indeed, `f`.

The `-print` flag can be passed to the `elpi` command line tool in order
to print the program after spilling.

## N-ary binders

The `pi` and `sigma` binders are n-ary:
- `sigma X Y\ t` is expanded to `sigma X\ sigma Y\ t`.
- `pi x y\ t` is expanded to `pi x\ pi y\ t`.

At the time of writing type annotation on `pi` variables are ignored by both
the interpreter and the `elpi-checker.elpi`.

## N-ary implication

The `=>` connectives accepts, on its left, a list of predicates.
For example `[p,q] => g` is equivalent to `(p, q) => g` that
is also equivalent to `q => p => g`.

This is particularly useful in writing [CHR rules](#syntactic-constraints)
since the hypothetical program is a list of clauses.

Note that this is also true for `:-`, i.e. its right hand side can
be a list of predicates.

## Non logical features

- The cut operator `!` is present, and does not work on nested disjunctions (`;` is not primitive).

- A built-in lets one collect data across search.  The primitives are
  `new_safe S`, `stash S T`, `open_safe S TL`.
  Note that `T` has to be ground and closed.  Safes are not effected by
  backtracking.  They can be used to log a computation / a list of failures.
  They are used, for example, in `elpi-checker.elpi` to log errors.

## Typechecking

Typing plays *no role at runtime*.  This differs from standard λProlog.
This also means that type annotations are totally optional.
Still, they greatly help `elpi-checker.elpi` to give reasonable errors.
Notes about `elpi-checker.elpi`:
- Inference of polymorphic predicates is not performed.
- `type foo list A -> prop` can be used to declare a polymorphic `foo`.
- `any` means any type.
- `variadic T1 T2` means an arbitrary number of `T1` to build a `T2` (for example `,` is of that type).
- Type declarations can be repeated to obtain simple overloading:
  ```
  type foo int -> prop.
  type foo string -> prop.
  main :- foo 1, foo "3". % typechecks
  ```
- `o` is written `prop`, since `o` is already used to mean output in `mode` (and `i` to mean input).

## Subterm naming

A subterm can be given a name using an `as Name` annotation.
The name must be a variable name, and such variable is assigned to
that subterm.
```prolog
lex-max (pair A B as L) (pair X Y     ) L :- A > X ; ( A = X, B >= Y).
lex-max (pair A B)      (pair X Y as R) R :- A < X ; ( A = X, B <= Y).
```

Limitation: `as` cannot be applied to the entire clause head.

## Clause grafting

Take this code, in a file called `lp-lib.elpi` providing general purpose
code, like a fatal error clause *named* "default-fatal-error" using the `:name`
attribute.
```prolog
:name "default-fatal-error" 
fatal-error Msg :- print Msg, halt.
```
One can, from any file accumulated after `lp-lib.elpi`, take over
such clause using the `:before` attribute.
```prolog
:name "my-fatal-error" :before "default-fatal-error"
fatal-error Msg :- !, M is "elpi: " ^ Msg, coq-err M.
```

The `:after` attribute is also available.

## Modes

Predicate arguments can be flagged as input as follows
```prolog
mode (pp i o).

pp (lambda Name F) S :- (pi x\ pp x Name => pp (F x) S1), S is "λ" ^ Name ^ "." ^ S1.
pp (app H A) S :- pp H S1, pp A S2, S is "(" ^ S1 ^ " " ^ S2 ^ ")".
pp ?? "_".
```

```
goal> pp (lambda "x" y\ app y y) S.
Success:
  S = "λx.(x x)"
goal> pp (lambda "x" y\ app W y) S.
Success:
  W = X0
  S = "λx.(_ x)"
```
Note that in the second example `W` is not instantiated.
When an argument is flagged as `i` then its value is
matched against the clauses' corresponding pattern.
`??` is the pattern for flexible input. Such flexible term can be
used in the rest of the clause by naming it with `as Name`

### Mode and type declaration

The short form
```prolog
pred foo i:int, o:string.
```
is expanded to the following declarations
```prolog
type  foo int -> string -> prop.
mode (foo i o).
```

## Syntactic constraints

A goal can be suspended on a list of variables with the `declare_constraint` 
built in.  In the following example the goal `even X` is suspended on the
variable `X`.
```prolog
goal> declare_constraint (even X) [X].
Success:
Constraints:
  even X  /* suspended on X */
```
Suspended goals are resumed as soon as any of the 
variables they are suspended on gets assigned.
```
goal> declare_constraint (even X) [X], X = 1.
Failure
```

Hypothetical clauses are kept:
```
goal> pi x\ sigma Y\ even x => declare_constraint (even Y) [Y].
Success:
Constraints:
 {x} : even x ?- even (W x)  /* suspended on W */

goal> pi x\ sigma Y\ even x => (declare_constraint (even Y) [Y], Y = x).
Success:
```

The `declare_constraint` built in is typically used in conjunction with `mode`
as follows:
```prolog
mode (even i).
even (?? as X) :- !, declare_constraint (even X) [X].
even 0.
even X :- X > 1, Y is X - 2, even Y.
```

The `constraint` directive gives control on the hypothetical part of the
program that is kept by the suspended goal and lets one express constraint
handling rules.

A "clique" of related predicates is declared with
```prolog
constraint foo bar ... {
  rule ...
}
```
The effect is that whenever a goal about `foo` or `bar`
is suspended (via `declare_constraint`) only its hypothetical
clauses about `foo` or `bar` are kept.

When one or more goals are suspended on lists of unification
variables with a non-empty intersection, 
the rules between curly braces apply.
In most cases it is useless to manipulate two goals 
that don't share any variable.  If it is not the case, one can
artificially add the same variable to all suspended goals. Eg.
```
master-key K => (even X, even Y).
even (?? as X) :- !, master-key K, declare_constraint (even X) [K,X].
```

#### Example
```prolog
mode (odd i).
mode (even i).

even (?? as X) :- !, declare_constraint (even X) [X].
odd  (?? as X) :- !, declare_constraint (odd X)  [X].
even 0.
odd 1.
even X :- X > 1, Y is X - 1, odd  Y.
odd  X :- X > 0, Y is X - 1, even Y.

constraint even odd {
  rule (even X) (odd X) <=> false.
}
```

```
goal> whatever => even X.
Constraints:
  even X  /* suspended on X */
goal> even X, odd X.
Failure
```
### Constraint Handling Rules

#### Syntax
Here `+` means one or more, `*` zero or more
```
CONSTRAINT ::= constraint CLIQUE { RULE* }
CLIQUE ::= NAME+
RULE ::= rule TO-MATCH TO-REMOVE ALIGN GUARD TO-ADD .
TO-MATCH  ::= SEQUENT*
ALIGN     ::= > VARIABLE ~ VARIABLE VARLIST
TO-REMOVE ::= \   SEQUENT+
TO-ADD    ::= <=> SEQUENT
GUARD     ::= TERM
VARLIST ::= ~ VARIABLE VARLIST |
SEQUENT ::= TERM | ( VARIABLE : COMPOUND-TERM ?- COMPOUND-TERM )
TERM ::= VARIABLE | NAME | ( COMPOUND-TERM )
NAME ::= foo | bar ...
VARIABLE ::= Foo | Bar ...
COMPOUND-TERM ::= ...
```

#### Example of first order rules

We compute GCD.  The `gcd` predicate hold a second variable, so that
we can compute GCDs of 2 sets of numbers: 99, 66 and 22 named X;
14 and 77 called Y.

```prolog
mode (gcd i i).

gcd A (?? as Group) :- declare_constraint (gcd A Group) Group.

% assert result is OK
gcd 11 group-1 :- print "group 1 solved".
gcd 7 group-2 :- print "group 2 solved".

main :- gcd 99 X, gcd 66 X, gcd 14 Y, gcd 22 X, gcd 77 Y,
        % we then force a resumption to check only GCDs are there
        X = group-1, Y = group-2.

constraint gcd {
  rule (gcd A _) \ (gcd B _) | (A = B).
  rule (gcd A _) \ (gcd B X) | (A < B) <=> (C is (B - A), gcd C X).
}

```

Constraints are resumed as regular delayed goals are.

#### Example of higher order rules

##### Automatic alignment

```prolog
mode (term i o).
term (app HD ARG) TGT :- term HD (arrow SRC TGT), term ARG SRC.
term (lam F) (arrow SRC TGT) :- pi x\ term x SRC => term (F x) TGT.
term (?? as X) T :- declare_constraint (term X T) [X].

constraint term {
  rule (EX : GX ?- term (uvar _ LX) TX)
     \ (EY : GY ?- term (uvar _ LY) TY)
     > LX ~ LY
     | (compatible GX LX GY LY CTXCONSTR)
   <=> (CTXCONSTR, TX = TY).
}

compatible _ [] _ [] true :- !.
compatible GX [X|XS] GY [Y|YS] (TX = TY, K) :-
 (GX => term X TX),
 (GY => term Y TY),
 !,
 compatible GX XS GY YS K.
compatible _ _ _ _ false.

main :-
  (term (lam x\ lam y\ app (app (F x y) x) y) T1),
  (term (lam y\ lam x\ app (app (F x y) y) x) T2).
```

Without the propagation rule the result to `main` would be
```
...
Constraints:
 {x0 x1} : term x1 X0, term x0 X1 ?- term (X2 x1 x0) (arr X1 (arr X0 X3))  /* suspended on X2 */ 
 {x0 x1} : term x1 X4, term x0 X5 ?- term (X2 x0 x1) (arr X5 (arr X4 X6))  /* suspended on X2 */
```

The propagation rule aligns the two sequents by finding the permutation
between `LX` and `LY` that must be duplicate free lists of names (i.e.
the variables on which the constraints are suspended must be in
the Lλ fragment.

Such permutation is applied to the matched constraints, hence
the guard and the new goal operate on terms all living in the
same name context.  

The result with the propagation rule enabled is
```
 {x0 x1} : term x1 X0, term x0 X0 ?- term (X1 x1 x0) (arr X0 (arr X0 X2))  /* suspended on X1 */
```

The variables used in the patterns must be disjoint and
exactly one of them (binding a list of names) has to specified
in the alignment directive.

##### Manual alignment

If the program goes outside Lλ, no automatic alignment is provided.
In such case the alignment directive must be omitted. The pattern for
the sequents can bind the set of eigen variables (an integer) and
one of them can be used to specify in which name context the new goal will
run.  Moreover, the guard is executed in the disjoint union of the named
contexts, i.e. the matched sequents will hare no names.  It is up to the guard
to generate terms that live in the named context chosen for the new goal.
Patterns can share variables.

Example of a rule that takes the canonical type of K and
puts it in the CtxActual by replacing all variables (in L)
by their actual values in V.

```prolog
% Uniqueness of typing
utc [] T1 [] T2 (unify-eq T1V T2) :- !, copy T1 T1V.
utc [N|NS] T1 [V|VS] T2 C :- !, copy N V => utc NS T1 VS T2 C.

canonical? [].
canonical? [N|NS] :- is_name N, not(mem NS N), canonical? NS.

constraint of {
 rule (E1 : G1 ?- of (uvar K L1) T1 _) % canonical
    \ (E2 : G2 ?- of (uvar K L2) T2 _) % actual
    | (canonical? L1, utc L1 T1 L2 T2 Condition)
  <=> (E2: G2 ?- Condition).
}
```

The new goal replaces the (duplicate) typing constrain on K
by a unification problem that checks that the canonical type
of K once applied the explicit substitution V is compatible 
with the actual type.

#### Operational Semantics

As soon as a new constraint C is declared:

1. Each rule (for the clique to which C belongs) is considered,
   in the order of declaration. Let's call it R.
2. All constraints suspended on a list of variables with a non-empty intersection with the one on which C is suspended are considered
   (in no specified order). Let's call them CS
3. if R has n patterns, then all permutations of n-1 elements of CS and C are
   generated. I.e. C is put in any possible position in a list of
   other constraints taken from CS, let's call one of such lists S.
4. The constraints in S are frozen, i.e. all flexible terms (X a1..an) 
   are replaced by (uvar cx [b1,..,bn]) where cx is a new constant for
   X and bi is the frozen term for ai. We now have SF.
5. Each sequent in SF is matched against the corresponding pattern in R.
   If matching fails, the rule is aborted and the next one is considered.
6. Depending on the alignment directive all terms are either put in the
   same name context (if the alignment is present), or spread in different
   name contexts.
7. The guard is run.  If it fails the rule is aborted and the next one
   is considered. It if succeeds all subsequent rules are aborted (*committed 
   choice*).
8. The new goal is resumed immediately (before any other active goal).
   If no alignment is given, then name context
   has to be specified and the goal is checked to live in such context,
   otherwise elpi gives an error.
   
The application of CHR rules follows the [refined operation semantics](https://en.wikipedia.org/wiki/Constraint_Handling_Rules).

## Quotations

Syntactic sugar to describe object terms is available via quotations
and anti-quotations.  Quotations are delimited by balanced curly
braces, at least two, as in `{{` and `}}` or `{{..{{` and `}}..}}`.
The system support one unnamed quotations and many named ones with
syntax `{{:name` .. `}}` where `name` is any non-space or `\n` character.

Quotations are elaborated before run-time.

The [coq-elpi](https://github.com/LPCIC/coq-elpi) software embeds elpi 
in Coq and provides a quatation for its terms. For example
```prolog
{{ nat -> bool }}
```
unfolds to
```prolog
prod _ (indt "...nat") x\ indt "...bool"
```
Where `"...nat"` is the real name of the nat data type,
and where `prod` and `indt` are term constructors.
    
Anti quotations are also possible, the syntax depends on
the parser of the language in the quotation, `lp:` here.
```prolog
prod "x" t x\ {{ nat -> lp:x * bool }}
```
unfolds to
```prolog
prod "x" t x\ prod _ (indt "...nat") y\
  app [indt "...prod", x, indt "...bool"]
```
Note: x is bound in ELPI and used inside the quotation.

## Namespaces

```prolog
toto 1.
namespace foo {
bar X :- toto 2 => baz X.
baz X :- toto X.
}
main :- foo.bar 2, foo.baz 1.
```

```prolog
namespace rev {
 pred aux i:list A, i:list A, o:list A.
 aux [X|XS] ACC R :- aux XS [X|ACC] R.
 aux [] L L.
}
pred rev i:list A, o:list A.
rev L RL  :- rev.aux L []  RL.
```

## Advanced modes

```prolog
mode (pp o i) xas print,
     (pp i o) xas parse.

infixl &&  128.
infixl '   255.

pp (F2 && G2) (and ' F1 ' G1) :- !, pp F2 F1, pp G2 G1.
pp A A.

main :-
   (pi x\ (pp "nice" x :- !) =>
      parse ((V1 && true) && "nice") (P1 x)),
   print P1,
   (pi x\ (pp "ugly" x :- !) =>
      print (P2 x) (P1 x)),
   print P2.
% P1 = x0 \ and ' (and ' V1 ' true) ' x0
% P2 = x0 \ (V2 && true) && "ugly"
```

`mode` lets one reuse the same code in different modes.
When an argument is in `input` no unification variable is
instantiated, unless it comes from an output (e.g. non linear
pattern, needed to make the `pp A A` line work).
Unification of input arguments is  called matching.

The mode directive has also the following effect on code generation:

position | predicate | code generation
---------|-----------|----------------------------------------------------
 goal | any | just run as is
 hyp | pp | index as pp, index as print and replace all occs (rec calls) of pp with print, index as parse and replace all occs of pp with parse
 hyp | print | index as print
 hyp | parse | index as parse

Users of `pp` can avoid duplication this way:

```
mode (pptac i o) xas printtac(pp -> print),
     (pptac o i) xas parsetac(pp -> parse).

pptac (tac T) (tac S) :- pp T S.
```

In matching mode a syntax to introspect unification variables
is provided:
```prolog
pp1 ?? :-             print "a variable".
pp2 (?? K) :-         print "with id " K.
pp3 (?? _ L) :-       print "with arguments " L.
pp4 (?? K L as V) :-  print "a flexible term " V.
```
Only `V` is a proper term, `K` and `L` are not.

## Accumulate with paths

Elpi accepts `accumulate "path".` (i.e. a string rather than an indent)
so that one can use `.` in a file or path name.

