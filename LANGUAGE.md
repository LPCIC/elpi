# A reminder of what is coded in ELPI

## Lambda Prolog

```
mode (pp i o) xas print,
     (pp o i) as parse.

pp (F2 && G2) (and ' F1 ' G1) :- pp F2 F1, pp G2 G1.
pp A A.

main :-
   (pi x\ pp "nice" x => parse ((V1 && true) && "nice") (P1 x)), $print P1,
   (pi x\ pp "ugly" x => pprint (P2 x) (P1 x)), $print P2
% P1 = x0 \ and ' (and ' V1 ' true) ' x0
% P2 = x0 \ (V2 && true) && "ugly"
```

`mode` lets one reuse the same code in different modes.
When an argument is in `input` no unification variable is
instantiated, unless it comes from an output (non linear pattern).
This is needed to make the `pp A A` line work.

The mode directive has also the following effect on code generation

- goal: parse/print/pp -> just run as is
- hyp: pp -> index as pp, index as print and replace all occs of pp with print,
             index as parse and replace all occs of pp with parse
- hyp: print/parse -> index as print/parse

Users of `pp` can avoid duplication this way:

```
mode (pptac i o) xas printtac(pp -> print),
     (pptac o i) xas parsetac(pp -> parse).

pptac (tac T) (tac S) :- pp T S.
```

In matching mode, an extra syntax to introspect unification variables
is provided:
```
pp1 ?? :-             $print "a variable"
pp2 (?? K) :-         $print "with id " K.
pp3 (?? _ L) :-       $print "with arguments " L.
pp4 (?? K L as V) :-  $print "a flexible term " V.
```
Normally, only `V` is accessible, `K` and `L` are not exposed.

The `as` clause is available everywhere, not just in matching mode.

## CHR

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
Everything can me omitted.

semantics:
- `m` is a sequent to be matched.
- `r` is a sequent to be matched and removed from the store.
- `guard` is goal that is run in a special runtime where unification variables
  coming from the constraints are frozen (replaced by fresh constants) and
  where pi constants are eventually aligned (see below).
- `new is a new goal to be injected in the main runtime (not necessarily a
  constraint).
- `x` is a variable.  If such variable denotes the arguments of a unification
  variable, then this list must be only made of constants (disjoint) and is
  used to align constraints.  If such variable denotes a unification variable
  without its arguments, then it means no-alignement but check the variable
  (key) is the same.

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

Here goals are not aligned, `> X ~ Y` can be removed if one places `X=Y` in the
guard, but having it there is more efficient.  Goals are not aligned, hence
pi-variables are spread (made so that there is no overlap between the ones of
the goals, not implemented).  No such variable has to appear in `new` (check no
implemented).  For this to work, `TX` and `TY` (in `compatible` hence in
in `new`) have to be closed.

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
`term (X (app f y)) T` gets suspended.

