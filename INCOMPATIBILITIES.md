Known incompatibilities with Teyjus
===================================

This file tries to summarize known incompatibilities between Elpi and Teyjus.

# Semantics

- `;` is not a built-in and behaves differently wrt `!`
- unification problems outside the pattern fragment are *not* delayed unless one passes the (deprecated) 
  `-delay-problems-outside-pattern-fragment` flag to `elpi`
- integers are 31 bits (25 bits in Teyjus); etc for floats ...

# Syntax

- Since Elpi 1.15 the default parser does not support the `infix` directive
- No syntax for negative numbers: `~ 2` is the unary minus applied to `2`,
  not the number `-2`. If you want to write `-2`, just write `-2` with no
  space in between.
- No support for `\OCTAL \OCTALOCTALOCTAL \xHEX \xHEXHEX`
- Strings must not contain newlines; instead
  `\n`, `\b`, `\t`, `\r`, `\\`, `\"`, `\'`, "" are recognized.
- Non-associative infix/prefix/postfix behave like their associative
  counterparts. In particular, if `@@` and `@@@` are two prefix operators
  with precedence `@@` > `@@@` then `(@@ @@@ @@ @@@ a)` is parsed nevertheless
- Elements of lists are parsed at level `120`, that is the first level used
  in` lp-syntax.elpi` after `110`, the level of `,`.
- `i<`, `r+`, etc. are polymorphic
- No support for `x :: : type l` and `x = : type y`.
- If a file ends (without `eol`) inside a comment, the parser ignores the 
  comment
  (in place of returning an error). The same happens if the query is not `.`
  terminated.
- No beta-redexes in the source code.

# Modules

- Module signatures are ignored.
- Elpi accumulates each file once; Teyjus does it multiple times, that is
  always bad (all clauses are duplicated and tried multiple times, that is
  rarely the expected behavior).
- Elpi understands relative paths as in `accumulate "../foo"`: resolution
  of relative paths is done according to the path of the accumulating file
  first or, if it fails, according to the TJPATH.
- No support for `import`.

