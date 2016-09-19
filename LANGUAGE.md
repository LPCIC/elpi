# A reminder of what is coded in ELPI

## Lambda Prolog

```
mode (pp o i) xas print,
     (pp i o) xas parse.

infixl &&  128.
infixl '   255.

pp (F2 && G2) (and ' F1 ' G1) :- !, pp F2 F1, pp G2 G1.
pp A A.

main :-
   (pi x\ (pp "nice" x :- !) =>
      parse ((V1 && true) && "nice") (P1 x)),
   $print P1,
   (pi x\ (pp "ugly" x :- !) =>
      print (P2 x) (P1 x)),
   $print P2.
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
---------+-----------+----------------------------------------------------
 goal    | any       | just run as is
---------+-----------+----------------------------------------------------
 hyp     | pp        | index as pp, index as print and replace all
         |           | occs (rec calls) of pp with print, index as parse
         |           | and replace all occs of pp with parse
---------+-----------+----------------------------------------------------
 hyp     | print     | index as print
         | parse     | index as parse
---------+-----------+----------------------------------------------------

Users of `pp` can avoid duplication this way:

```
mode (pptac i o) xas printtac(pp -> print),
     (pptac o i) xas parsetac(pp -> parse).

pptac (tac T) (tac S) :- pp T S.
```

In matching mode a syntax to introspect unification variables
is provided:
```
pp1 ?? :-             $print "a variable"
pp2 (?? K) :-         $print "with id " K.
pp3 (?? _ L) :-       $print "with arguments " L.
pp4 (?? K L as V) :-  $print "a flexible term " V.
```
Only `V` is a proper term, `K` and `L` are not.

The `as` clause is available everywhere, not just in matching mode,
but not on the top level term: `foo X as G :- ..` is not supported (error NYI).

## delay and constraint

Goals can be delayed on a (list of) flexible terms.

```
mypred (?? as K) :- $delay (mypred K) K.
another (?? as K) :- $constraint (another K) K.
```

Delayed goals are resumed as soon as (one of) the key(s) is instantiated,
i.e. resumed goals are put in head position in the and-list and are processed
at the next SLD step.

Constraints do receive a special treatment: their proof context is
filtered according to the clique they are declared in and they are
manipulated by CHR rules (see CHR section).

### CHR

```
constrant c1..cn {
  rule (m1)..(mn) \ (r1)..(rm) > x1 ~ x2 .. ~ xn | guard <=> new.
  rule ...
}
```

where `m` and `r` are sequents as in `(goal)` or `(ctx ?- concl)`,
`guard` and `new` are goals and `x` is a variable name. `c` is a constraint
name (head symbol).  The set of `c` defines a constraint clique.
CHR rules belonging to the block do apply to the clique, and constraints
in the clique have their context filtered to only contain stuff in the clique.
Every component (m, r, x, guard, new) can me omitted.

semantics:
- `m` is a sequent to be matched.
- `r` is a sequent to be matched and removed from the store.
- `guard` is goal that is run in a special runtime where unification variables
  coming from the constraints are frozen (replaced by fresh constants) and
  where pi constants are eventually aligned (see below).
- `new` is a new goal to be injected in the main runtime (not necessarily a
  constraint) and lives in the initial context.
- `x` is a variable.  If such variable denotes the arguments of a unification
  variable, then this list must be only made of constants (disjoint) and is
  used to align constraints.  If such variable denotes a unification variable
  without its arguments, then it means no-alignement but check the variable
  (key) is the same.

`m` and `r` must use disjoint sets of variables, `guard` is executed after
the alignment and can thus mix variables coming from different goals.

CHR application loops until

### Example 0

We compute GCD.  The `gcd` predicate hold a second variable, so that
we can compute GCDs of 2 sets of numbers: 99, 66 and 22 named X;
14 and 77 called Y.

```
mode (gcd i i).

gcd A (?? as B) :- $constraint (gcd A B) B.

% assert result is OK
gcd 11 group-1 :- $print "group 1 solved".
gcd 7 group-2 :- $print "group 2 solved".

main :- gcd 99 X, gcd 66 X, gcd 14 Y, gcd 22 X, gcd 77 Y,
        % we then force a resumption to check only GCDs are there
        X = group-1, Y = group-2.

constraint gcd {
  rule (gcd A X) \ (gcd B Y) > X ~ Y | (A = B).
  rule (gcd A X) \ (gcd B Y) > X ~ Y | (A < B) <=> (C is (B - A), gcd C X).
}

```

The alignment condition is used to apply the rule to constraints in the same
set.  Constraints are resumed as regular delayed goals are.


### Example 1

```
constraint term {
  rule (GX ?- term (?? X LX) TX)
     \ (GY ?- term (?? Y LY) TY)
     > X ~ Y
     | (compatible GX LX GY LY CTXCONSTR)
   <=> (CTXCONSTR, TX = TY).
}

compatible _ [] _ [] true :- !.
compatible GX [X|XS] GY [Y|YS] (TX = TY, K) :-
 (GX ====> term X TX),
 (GY ====> term Y TY),
 !,
 compatible GX XS GY YS K.
compatible _ _ _ _ false.
```

Goals are not aligned, hence pi-variables are spread (made so that there is no
overlap between the ones of the goals, NYI).  No such variable has to appear in
`new` (NYI).  For this to work, `TX` and `TY` (in `compatible` hence in in
`new`) have to be closed.

TBD.

### Example 2

```
constraint term {
  rule (GX ?- term (?? _ LX as KX) TX)
     \ (GY ?- term (?? _ LY as KY) TY)
     > KX ~ KY
     | (compatible GX LX GY LY CTXCONSTR)
   <=> (CTXCONSTR, TX = TY).
}
compatible _ [] _ [] true :- !.
compatible GX [X|XS] GY [Y|YS] (TX = TY, K) :-
 (GX ====> term X TX),
 (GY ====> term Y TY),
 !,
 compatible GX XS GY YS K.
compatible _ _ _ _ false.
```

This time `LX` and `LY` are used to align the goals and it is now legit
to inject `TX = TY` in the main runtime.  This fails if something like
`term (X (app f y)) T` gets suspended, since alignment only works
in the l-lambda fragment.

## Sugar

- `sigma X Y\ t` is expanded to `sigma X\ sigma Y\ t`.
- `pi x y\ t` is expanded to `pi x\ pi y\ t`.

- `constraint (foo X) on X` is expanded to
  `foo (?? as X) :- $constraint (foo X) X`


