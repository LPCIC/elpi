# Extensions to λProlog implemented in ELPI

ELPI is still a young language and the features below are not specified very
formally. Please refrain from relying on behaviors that are not explicitly
described (but happen to work for you). Help in improving this very brief doc
is very welcome. Questions or feature requests are welcome as well.

- [Underscore](#underscore) is a real wildcard

- [Implication](#implication) has the *right precedence*™

- [Spilling](#spilling) turns `..{foo X}..` into `foo X Y,..Y..`

- [N-ary binders](#n-ary-binders) let one write `pi x y z\ ...`

- [N-ary implication](#n-ary-implication) let one write `[p,q] => g`

- [Non logical features](#non-logical-features) like `!` or `new_safe`

- [Typechecking](#typechecking) is performed by `elpi-checker.elpi`
  on the quoted syntax of the program and query

- [Subterm naming](#subterm-naming) can be performed
  using an `as X` annotation in the head of a clause

- [Clause grafting](#clause-grafting) can inject a clause
  in the middle of an existing program

- [Conditional compilation](#conditional-compilation) can be used
  to conditionally consider/discard clauses or CHR rules

- [Configurable argument indexing](#configurable-argument-indexing) can be used
  to write code in a more natural way and still get good performances

- [Modes](#modes) can be declared in order to control the generative
  semantics of Prolog

- [Determinacy checking](#determinacy-checking) ensures that predicates marked
  as functional behave as single-valued relations and that their outputs
  have the expected determinacy.

- [Syntactic constraints](#syntactic-constraints) are goals suspended on
  a set of variables that are resumed when any of them gets assigned and
  that can be manipulated by CHR like rules

- [Quotations](#quotations) let you write terms in a custom syntax and
   have ELPI translate them into λProlog terms.  This is only available
   via the OCaml API.

- [Namespaces](#namespaces) are to avoid name conflicts. This is a very
  simple syntactic facility to add a prefix to all names declared in a
  specific region. It is complemented by the shorten directive that lets
  one use a short name for a symbol in a namespace.

- [Accumulate with paths](#accumulate-with-paths) accepts `accumulate "path".`
  so that one can use `.` in a file/path name.

- [Tracing facility](#tracing-facility) to debug your programs.
 
- [Macros](#macros) are expanded at compilation time
 
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
On the contrary a problem like `DummyNameUsedOnlyOnce = something` demands the
computation of the solution (even if it is not used), and hence can *fail* if
some variable occurring in something is out of scope for `DummyNameUsedOnlyOnce`.

Side note: `elpi-checker.elpi` (see below) reports warnings about linearly used
variables, suggesting to start their name with `_` (`_Name` is just sugar for `_`).

## Implication

In standard λProlog the infix `=>` binds stronger than `,` and as a consequence
`a, b => c, d` reads `a, (b => c), d`. According to our experience this tricks
beginners, for example the following attempt to add a debugging print has a
catastrophic effect.
```prolog
buggy :- p => q.
buggy :- p => print "debug print", q.
```

Elpi warn if `=>` is used without parentheses, and provides the infix `==>`
that binds stronger than `,` only in the left, i.e. `a, b ==> c, d` reads
`a, (b ==> (c, d))`.

### Automatic tail Cut

The [determinacy checking](#determinacy-checking) is not complete and sometimes
it emits a warning about hypothetical clauses overlapping with other clauses.
One way to silence the warning without exlicitly writing a tail cut is to use
the `=!=>` operator, that automatically adds a tail cut.
```prolog
main :- copy a b =!=> copy T U.
main :- (copy a b :- !) ==> copy T U. % equivalent
```
Note that `=!=>` may need to add the cut at runtime, eg when the hypothetical
clause is not known statically
```prolog
main :- X = copy a b, X =!=> copy T U. % still cuts at run time
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

Spilling implication works as well.
```prolog
foo R :- R = lam x\ g {foo x => mk-app f [x,g x]}.
```
rewrites to
```prolog
foo R :- (pi x\ foo x => mk-app f [x,g x] (Spilled_1 x)), R = lam x\ g (Spilled_1 x).
```

Spilling a conjunction has the effect of spilling the last conjunct.
```prolog
foo R :- R = lam x\ g {h x, mk-app f [x,g x]}.
```
rewrites to
```prolog
foo R :- (pi x\ h x, mk-app f [x,g x] (Spilled_1 x)), R = lam x\ g (Spilled_1 x).
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
  `new_safe S`, `stash_in_safe S T`, `open_safe S TL`.
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
  Anyway `o` is accepted in type declarations and is translated on the fly to `prop`.
- constants with no associated type generate a warning
  - unless the name of the full name of the constant (after namespace
    elimination) is `main` or ends in `.aux` or contains `.aux.`

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

The `:after`, `:replace` and `:remove` attributes is also available.

The `:replace` and `:remove` attribute cannot be given to a named clause.
This is to avoid the following ambiguity:

```prolog
:name "replace-me"
p 1.

% from one accumulated file
:replace "replace-me" :name "replace-me"
p 2.

% from another accumulated file
:replace "replace-me" :name "replace-me"
p 3.
```
Here the order in which replacement is performed would matter.

Both `:replace:` and `:remove` can only apply to rules for the same predicate.
Example:

```prolog
:name "this" p 1.

:remove "this" p _. % OK
:remove "this" q _. % Error
```


## Conditional compilation

The following λProlog idiom is quite useful to debug code:
```prolog
% pred X :- print "running pred on " X, fail. % uncomment for debugging
pred X :- ...
```
By removing the comment sign in front of the first clause one gets some
trace of what the program is doing.

In Elpi this can be written using the `:if` clause attribute
(reminiscent of the C `#ifdef` preprocessing directive).

```prolog
:if "DEBUG" pred X :- print "running pred on " X, fail.
pred X :- ...
```

The debug clause is discarded *unless* the compilation variable `DEBUG`
is defined.  The `elpi` command line interpreter understands `-D DEBUG`
to define the `DEBUG` variable (and consequently keep the debugging code).

Here `DEBUG` is just arbitrary string, and multiple `-D` flags can be passed
to `elpi`.

The attribute `:if` can also be used on CHR rules.

### Compatibility ifdefs

It is also possible ask the lexer to discard text before it reaches the parser.

```prolog
% elpi:if version < 2.0.0
This text is ignored if the version of Elpi old
% elpi:endif
```

Currently the only supported expression is `version <component>` where
`<component>` defaults to `elpi`. The OCaml APIs let one declare the version
of other components of the host application that may affect the code to
be parsed.
The expression and it must be placed on the left of the operator
(either `<` or `>` or `=` or `<=` or `>=`) and ifdefs cannot
be nested.

If not available (e.g. `dune subst` did not run) the version of `elpi`
defaults to `99.99.99`.

One can also ask the lexer to always skip some text. That can be useful if one
wants to keep around code that is not meant for Elpi (but for example for Teyjus).

```prolog
% elpi:skip 2
infixr ==> 120. % directive not supported by Elpi
infixr || 120. % last line being skipped
```

## Configurable argument indexing

By default the clauses for a predicate are indexed by looking
at their first argument at depth 1. The `:index` attribute lets
one specify a different argument and/or a different indexing technique.
The syntax is
```
:index (<arg-spec>) "index-type"
```
where `<arg-spec>` is a list of numbers or `_`, and `"index-type"` is an
optional string. Values supported are `"Map"` (tree map over constants, standard
Prolog indexing), `"Hash"` (see below) and `"DTree"` (see below).

For example:
```prolog
:index(_ 1)
pred mymap i:(A -> B), i:list A, o:list B.
mymap F [] [].
mymap F [X|XS] [Y|YS] :- Y = F X, mymap XS YS.
```
Here `(_ 1)` is a shorthand for `(0 1)` that means index at depth 0 the first
argument (that means don't index it), at depth 1 the second argument and at depth
0 all the remaining ones.

If only one argument is indexed, and it is indexed at depth one, then Elpi uses
a standard indexing technique based on a binary search tree, i.e.
the `"Map"` index-type.

### Discrimination tree index

If one argument is indexed at depth greater than one, or more arguments
are indexed at any depth, then Elpi uses
a [discrimination tree](https://www.cs.cmu.edu/~fp/courses/99-atp/lectures/lecture28.html).
Both the rule argument and the goal argument are
indexed up to the given depth.

Indexed terms are linearized into paths. Paths are inserted into a trie data
structure sharing common prefixes.

One can force this index even if only one term is indexed by using the directive
`:index (...) "DTree"`.

### Hash based index

If more than one argument is indexed then Elpi can use an index based on the idea of
[unification hashes](http://blog.ndrix.com/2013/03/prolog-unification-hashes.html).
To exable it one has to use the `:index (...) "Hash"` directive.

```prolog
:index (2) "Hash"
pred mult o:nat, o:nat, o:nat.
mult o X o.
mult (s (s o)) X C :- plus X X C.
mult (s A) B C :- mult A B R, plus B R C.
```

The hash value, a list of bits, is generated hierarchically and up to the
specified depth. Unification variables in a clause head are mapped to a
sequence of `1`, while they are mapped to a sequence of `0` when they are part of
the query. Constants are mapped
to a hash value, a sequence of both `1` and `0`. If the bit wise conjunction `&` of the
hash of the query and the hash of the head of a clause is equal to the hash of
the query, then the clause is selected.

Intuitively:
- in a clause `1` means "I provide this piece of info"
- in the query `1` means "I demand this piece of info"

A flexible query is made of `0`s, hence it demands nothing, since `0 & x = 0`
(`x` is a bit of the clause). Conversely a flexible clause is made of `1`s,
hence it provides anything, since `x & 1 = x` (`x` is a bit of the query).

Example:
```
hash o = 1001 1011
hash s = 1011 0010

clauses: hashes are left trimmed to fit word size, here 8
  
  1: mult o         = 1001 1011
  2: mult (s (s o)) = 0010 0010
  3: mult (s A)     = 0010 1111

goal: if hgoal & hclause = hgoal then it is a match
     mult (s o)     = 0010 1011 % only 3 matches
     mult (s X)     = 0010 0000 % 2 and 3 match
     mult X         = 0000 0000 % 1, 2 and 4 match
```

In our (limited) testing unification hashes are on-par with the standard
indexing technique, but they provide grater flexibility. The only downside is
that hard to predict collisions can happen (the entire hash must fit one word).

## Modes

Predicate arguments can be flagged as input as follows
```prolog
mode (pp i o).

pp (lambda Name F) S :- (pi x\ pp x Name => pp (F x) S1), S is "λ" ^ Name ^ "." ^ S1.
pp (app H A) S :- pp H S1, pp A S2, S is "(" ^ S1 ^ " " ^ S2 ^ ")".
pp uvar "_".
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
`uvar` is the pattern for flexible input. Such flexible term can be
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

## Determinacy checking

Determinacy is the property of a predicate to produce at most one result. This
means that the predicate behaves as a single-valued relation or a function.
Operationally, a the call to a functional predicate does not generate additional
choice points.

The signature of predicates defines their behavior with respect to determinacy.

The syntax:

```prolog
func PRED_NAME? COMMA_SEPARATED(types*) -> COMMA_SEPARATED(types*).
```

uses the keyword `func` instead of `pred`. It introduces the signature of a new
deterministic predicate called `PRED_NAME`. The types of its input (respectively
output) arguments appear before (respectively after) the `->` symbol. Note that
`PRED_NAME` is optional. If not specified, the signature represents the type of
anonymous functions.

For example, in the following code:

```prolog
func id (func A -> B), A -> B.
id P X Y :- P X Y.
```

`id` is a function that takes as input an (anonymous) binary function from
`A` to `B`, a second input of type `A`, and produces an output of type `B`.

We also accepts the syntax:

```prolog
func PRED_NAME? COMMA_SEPARATED(types*).
```

where the `->` is omitted. In this case we are declaring a predicate
(or anonymous predicate) with no outputs — i.e., all arguments
are in input mode.

It is possible to declare functions with mixed input-output arguments, where
output arguments may appear between input arguments. In such cases, the user
should use the standard `pred` syntax along with the `:functional` attribute.

For example, the signature of the `is` predicate can be written as:

```prolog
:functional pred (is) o:A, i:A.
```

Internally the keyword `fprop`, akin to `prop`, is used in the type of symbols
that are functional predicate (it may show up in error messages).

The static checker is built around a notion of "subtyping" since a function is
(mathematically) a relation, but the converse is not true. We say that a function
is stronger than a relation.

Signatures a compared using the function $\subseteq : D \to D \to
bool$, where $D$ is the type of signatures. In a call like $d_1 \subseteq d_2$,
the result is true if $d_1$ is a signature that is stronger than or equal to
$d_2$ (equivalently, $d_2$ is weaker than or equal to $d_1$).

The function $\subseteq$ is implemented as follows:

$$
\begin{align}
func &\subseteq pred\\
l_1 \to_i r_1 &\subseteq  l_2 \to_i r_2 \qquad\mathrm{ if\ } l_2 \subseteq l_1 \land r_1 \subseteq r_2\\
l_1 \to_o r_1 &\subseteq  l_2 \to_o r_2 \qquad\mathrm{ if\ } l_1 \subseteq l_2 \land r_1 \subseteq r_2\\
\end{align}
$$

This function mirrors the subtyping relation, as we use the contravariant
relation for inputs.

We say that a predicate $p$ is *wrongly* called if one of its inputs has an
inferred determinacy weaker than the expected one. In this case, if $p$ is a
function, we cannot guarantee that the call will behave deterministically.

For example, consider the following program.

```prolog
pred likes i:guest, o:dishes.
likes mario pizza.
likes mario pasta.
likes anna gelato.
```

The call `id likes mario A` is *wrongly* called since the input `likes` has a
determinacy which is weaker then the expected by `id`. You can remark that the
call assigs `A` to `pizza` but leave a choice point with `A` assigned to
`pasta`.

Our notion of determinacy not only provides guarantees about the behavior of a
call $c$, but also about the signature of the outputs of that call $c$.

For example, one can define:
```prolog
func make-deterministic (pred i:A, o:B) -> (func A -> B).
make-deterministic P (x\y\ P x y, !).
```
which transforms a binary predicate into a binary function (note the `!`). This
means that the call `make-deterministic likes X` is deterministic.
The inferred determinacy of `likes` is `pred i:guest o:dishes`, which is 
equivalent to `pred i:A, o:B`. This ensures that the call is deterministic.
Moreover, we are guaranteed that `X` will be a binary function with the type
`func guest -> dishes`. If we use the same `X` in the call `id X mario A`,
we can observe that `id` is *correctly* called. Therefore, it
behaves deterministically, and `A` is assigned the only value
`pizza`.

Let's consider an other example:

```elpi
func map list A, (func A -> B) -> list B.
```

This signature tells that in a call like `map L F R`, if `F` is a binary
function from `A` to `B`, then the interpretation of `map L F R` produces no
choice points. For instance, consider the following code:

```prolog
func likes! A -> B.
likes! A B :- likes A B, !.

func map list A, (func A -> B) -> list B.
map [] [].
map [X|XS] F [Y|YS] :- F X Y, map XS F YS.
```
The call `map [mario,anna] likes! L` is deterministic and produces exactly one
result: `L = [pizza,gelato]`. However, the call `map [mario,anna] likes L` is
not deterministic because it is "wrongly" called (`likes` is not a binary
function). This call produces an initial result `L = [pizza,gelato]` but
leaves one additional choice point where `L` is assigned to `[pasta,gelato]`.


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
even (uvar as X) :- !, declare_constraint (even X) [X].
even 0.
even X :- X > 1, Y is X - 2, even Y.
```

The `constraint` directive gives control on the hypothetical part of the
program that is kept by the suspended goal and lets one express constraint
handling rules.

A new constraint can be declared with the following syntax:
```prolog
constraint p1 p2 p3 ?- foo bar {
  rule (Ctx ?- foo Arg1) | ... <=> (Ctx => bar Arg1)
}
```

> [!IMPORTANT]
> When a suspended goal (via `declare_constraint`) is resumed, only the rules
implementing the symbols passed in the head of the constraint are kept. 

In our example, only the rules for `p1, p2, p3, foo` and `bar` are kept.
Therefore, if just before the suspension of the goal `foo x` a rule like `p4`
exists, this rule will be filtered out from the context of the suspended goal.

The symbol `?-` separates two lists of
predicate names: the former list is a predicate filter for the context;
the latter list is a predicate filer for the goal.

In the example above, the rules implementing `p1`, `p2` and `p3` are kep in
in the suspended goal context. Therefore, when
solving the goal  `Ctx => bar Arg1` all the rules for these three predicates are
part of `Ctx`.

The list of predicate names after the `?-` should form a "clique", a set of
symbols disjoint from all the other cliques in the constraint store. If two
overlapping cliques are detected, the fatal error *overlapping constraint
cliques* is raised. The overlapping check is not applied to the context filters,
that is, in the case of two constraints declared
on two same cliques `c` with different filters `h1` and `h2`, then the two
filters are merged and added to the clique `c`.

For example, if we keep the example above, the following code snipped would
correctly extend the previous constraint:

```
constraint p4 ?- foo bar {
  rule ...
}
```

From now on, all the goals suspended on the predicates `foo` and `bar` will see
in their contexts the all the rules implementing the predicates `p1, p2,
p3, p4` = $\{$`p1,p2,p3`$\} \cup \{$`p4`$\}$.

> [!NOTE]
> If the list of predicate names before `?-` is empty, then the `?-` can be omitted  

Example: `constraint foo bar { ... }`. In this case the new suspended goals
talking about `foo` and `bar` will consider the rules for the predicates `p1,
p2, p3` = $\{$`p1,p2,p3`$\} \cup \varnothing$.

Finally `constraint foo bax { ... }.` raise the overlapping clique error, since
this constraint set intersect with another clique, i.e. $\{$`foo,bax`$\} \cap
\{$`foo, bar`$\} \neq \varnothing$. 

When one or more goals are suspended on lists of unification
variables with a non-empty intersection, 
the rules between curly braces apply.
In most cases it is useless to manipulate two goals 
that don't share any variable.  If it is not the case, that is, one
wants an artificial key common to all goals, one can
put `_` as one of the keys.
```
even (uvar as X) :- !, declare_constraint (even X) [_,X].
```
Constraints keyed on `[_]` are never resumed.

Constraints keyed on `[]` are never combined with other
constraints.

Rules can be given a name using the `:name` attribute.
It is used only in debug output.

#### Example
```prolog
mode (odd i).
mode (even i).

even (uvar as X) :- !, declare_constraint (even X) [X].
odd  (uvar as X) :- !, declare_constraint (odd X)  [X].
even 0.
odd 1.
even X :- X > 1, Y is X - 1, odd  Y.
odd  X :- X > 0, Y is X - 1, even Y.

constraint even odd {
  :name "even is not odd"
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
CTX_FILTER ::= CLIQUE ?-
CONSTRAINT ::= constraint CTX_FILTER? CLIQUE { RULE* }
CLIQUE ::= NAME+
RULE ::= rule TO-MATCH TO-REMOVE GUARD TO-ADD .
TO-MATCH  ::= SEQUENT*
TO-REMOVE ::= \   SEQUENT+
TO-ADD    ::= <=> SEQUENT
GUARD     ::= TERM
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

gcd A (uvar as Group) :- declare_constraint (gcd A Group) Group.

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

```prolog
mode (term i o).
term (app HD ARG) TGT :- term HD (arrow SRC TGT), term ARG SRC.
term (lam F) (arrow SRC TGT) :- pi x\ term x SRC => term (F x) TGT.
term (uvar as X) T :- declare_constraint (term X T) [X].

constraint term {
  rule (GX ?- term (uvar K LX) TX)
     \ (GY ?- term (uvar K LY) TY)
     | (compatible GX LX GY LY CTXEQS)
   <=> [TX = TY | CTXEQS].
}

compatible _ [] _ [] [] :- !.
compatible GX [X|XS] GY [Y|YS] [TX = TY | K] :-
 (GX => term X TX),
 (GY => term Y TY),
 !,
 compatible GX XS GY YS K.
compatible _ _ _ _ [].

main :-
  (term (lam x\ lam y\ app (app (F x y) x) y) T1),
  (term (lam y\ lam x\ app (app (F x y) y) x) T2).
```

*Without* the propagation rule the result to `main` would be:
```
...
Constraints:
 {x0 x1} : term x1 X0, term x0 X1 ?- term (X2 x1 x0) (arr X1 (arr X0 X3))  /* suspended on X2 */ 
 {x0 x1} : term x1 X4, term x0 X5 ?- term (X2 x0 x1) (arr X5 (arr X4 X6))  /* suspended on X2 */
```

The result *with* the propagation rule enabled is:
```
 {x0 x1} : term x1 X0, term x0 X0 ?- term (X1 x1 x0) (arr X0 (arr X0 X2))  /* suspended on X1 */
```

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
6. All terms are spread in different name contexts, and now live in the
   disjoint union of all name contexts.
7. The guard is run.  If it fails the rule is aborted and the next one
   is considered. It if succeeds all subsequent rules are aborted (*committed 
   choice*).
8. The new goal is resumed immediately (before any other active goal).
   If the name context for the new goal is given, then the new goal
   is checked to live in such context before resuming.  If the name
   context is not specified the resumed goals lives in the disjoint union
   of all name contexts (*).
   
The application of CHR rules follows the [refined operational semantics](https://en.wikipedia.org/wiki/Constraint_Handling_Rules).

(*) The name context `C` is the first component of the sequent, eg
`C : G ?- P`. `C` is unified with the list of eigen variables, that is
`[c0, c1, .. cn]`. 

## Quotations

Syntactic sugar to describe object terms is available via quotations
and anti-quotations.  Quotations are delimited by balanced curly
braces, at least two, as in `{{` and `}}` or `{{..{{` and `}}..}}`.
The system support one unnamed quotations and many named ones with
syntax `{{:name` .. `}}` where `name` is any non-space or `\n` character.

Quotations are elaborated before run-time.

The [coq-elpi](https://github.com/LPCIC/coq-elpi) software embeds elpi 
in Coq and provides a quotation for its terms. For example
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

Everything defined inside a namespace block gets prefixed by the
name of the namespace. For example

```prolog
toto 1.
namespace foo {
bar X :- toto 2 => baz X.
baz X :- toto X.
}
main :- foo.bar 2, foo.baz 1.
```

is equivalent to

```prolog
toto 1.
foo.bar X :- toto 2 => foo.baz X.
foo.baz X :- toto X.
main :- foo.bar 2, foo.baz 1.
```

Note that  if a clause for `toto` was defined inside the namespace,
then the symbol would have been considered as part of the namespace.

```prolog
toto 1.
namespace foo {
toto 3.
bar X :- toto 2 => baz X.
baz X :- toto X.
}
main :- foo.bar 2, foo.baz 1.
```

is equivalent to

```prolog
toto 1. % this one is no more in the game
foo.toto 3.
foo.bar X :- foo.toto 2 => foo.baz X.
foo.baz X :- foo.toto X.
main :- foo.bar 2, foo.baz 1.
```

### shortening names from a namespace

Names from a namespace can be shortened by using
the `shorten` directive as follows.

```prolog
namespace list {
  append A B C :- ...
  rev L RL :- ...
}

shorten list.{ append }.

main :- append L1 L2 R. 
```

The part of the namespace before `{` is elided, what is inside is kept.
For example:

```prolog
shorten my.{ long.name }.
shorten my.long.{ othername }.

main :- long.name, othername. 
```
the body of `main` is equivalent to
```prolog
main :- my.long.name, my.long.othername. 
```

The scope of the `shorten` directive ends with the current file or
with the end of the enclosing code block.

```prolog
namespace stuff {
  shorten list.{ rev }.
  code :- ...
} % end of shorten list.rev.

main :- stuff.code, list.rev L1 L2 R. % only long name is accessible
```

The `shorten` directive accepts a "trie" of qualified names
with the following syntax.
```prolog
shorten std.{ list.map, string.{ concat, escape }}.

main :- list.map F [], concat "a" "b" AB, escape "x y" E.
```
Here `main` calls `std.list.map`, `std.string.concat` and finally
`std.string.escape`.

## Accumulate with paths

Elpi accepts `accumulate "path".` (i.e. a string rather than an indent)
so that one can use `.` in a file or path name.

## Tracing facility

Elpi comes with a tracing facility.  The feature was designed to debug
the interpreter itself, but can be used to debug user programs as well.

First of all the command line option `-trace-on` turns tracing on. This
impacts performances but enables trace points and their counters. Trace
points relevant for user programs are named `run`, `select` and `assign`.
Counters holding the number of times a trace point is reached can be
accessed using the `counter` builtin: one can print the value of these
counters in a program, but if `-trace-on` is not passed the value is `0`.

Once traces are on, one can control when tracing information is print.

The option `-trace-only` takes (a regular expression matching) the name
of of the trace point for which trace printing is enabled.
Eg `-trace-only '\(run\|assign\|select\)'`. The option can be repeated.

The option `-trace-only-pred` takes (a regular expression matching) the name
of a λProlog predicate: trace printing is enabled only when the current goal
predicate is matched. The option can be repeated.

The option `-trace-at` can be used to trace only a portion of the execution.
It takes a trace point name and two integers. Eg `-trace-at run 37 42` enables
traces between the 37th time and the 42nd time the `run` trace point is reached.
The option must be given in order to enable prints. If it is not given counters
are still updated, but nothing extra is print.

The `-no-tc` option has nothing to do with traces but disables the execution
of `elpi-checker` that being a λProlog program would be traced too resulting in a confusing trace.

Example program:
```prolog
a X :-d, b X, d.

b 0.
b N :- M is N - 1, d, b M.

d.

main :- a 2.
```

Example trace:
```shell
$ ./elpi a.elpi -test -trace-on -trace-at run 1 99 -trace-only '\(run\|assign\|select\)' -trace-only-pred b -no-tc
loading a.elpi (56a477507a974c95bd4cc9262b64bf84)
run 4 {{{ 
 run-goal = b 2
}}} ->  (0.000s)
select 4 {{{ b A0 :- (A1 is A0 - 1), d, (b A1).
  assign = A0 := 2
}}} ->  (0.000s)
 run 9 {{{ 
  run-goal = b 1
 }}} ->  (0.000s)
 select 8 {{{ b A0 :- (A1 is A0 - 1), d, (b A1).
    assign = A0 := 1
 }}} ->  (0.000s)
  run 14 {{{ 
   run-goal = b 0
  }}} ->  (0.000s)
  select 12 {{{ b 0 :- .| b A0 :- (A1 is A0 - 1), d, (b A1).
  }}} ->  (0.000s)

Success:
...
```

Note that `a`, `d`, and `main` are not part of the trace, that is instead
focused on the predicate `b`. Also note that `select` prints the list of
clauses that will be tried (separated by `|`).
Finally `assign` prints the terms assigned to variables.

Each trace point name is followed by the value of the corresponding counter.
One can use these numbers to refine the tracing options.

Example of the trace between steps 9 and 14 also including predicate `d`.

```shell
$ ./elpi a.elpi -test -trace-on -trace-at run 9 14 -trace-only '\(run\|assign\|select\)' -trace-only-pred '\(b\|d\)' -no-tc
loading a.elpi (56a477507a974c95bd4cc9262b64bf84)
run 9 {{{ 
 run-goal = b 1
}}} ->  (0.000s)
select 8 {{{ b A0 :- (A1 is A0 - 1), d, (b A1).
   assign = A0 := 1
}}} ->  (0.000s)
 run 13 {{{ 
  run-goal = d
 }}} ->  (0.000s)
 select 11 {{{ d  :- .
 }}} ->  (0.000s)
 run 14 {{{ 
  run-goal = b 0
 }}} ->  (0.000s)
 select 12 {{{ b 0 :- .| b A0 :- (A1 is A0 - 1), d, (b A1).
 }}} ->  (0.000s)

Success:
```

The command `elpi -help` prints all trace related options.

## Macros

A macro is declared with the following syntax
```prolog
macro @name Args :- Body.
```
It is expanded at compilation time. 

#### Example: literlas

```prolog
macro @path :- ["home","gares","elpi"].

main :- print @path.
```

#### Example: factor hypothetical clauses.
```prolog
macro @of X N T :- (of X T, pp X N).
of (lambda Name   F) (arr A B) :-         pi x\ @of x Name A =>            of (F x) B.
of (let-in Name V F) R         :- of V T, pi x\ @of x Name T => val x V => of (F x) R.
```
