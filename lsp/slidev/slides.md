---
title: Elpi in Slidev
---

# Elpi in Slidev

Editable Elpi code with diagnostics and hover, and runnable `main`.

See `README.md`.

---

# An editor

Errors and warnings are underlined as you type; hover a symbol for its type.

```elpi {monaco}
pred age -> string, int.
age "bob" 23.
age "alice" "twenty".
```

---

# A runnable editor

`main` runs when the slide loads and on every edit.

```elpi {monaco-run}
main :- std.map [1,2,3] (x\ y\ y is x * 2) L, print L.
```

```elpi {monaco-run}
main :- 1 = 2.
```

---

# Code from a file, output on the right

Full file

<<< @/snippets/example.elpi

The same, with the facts folded (`% hidden:` ... `% hidden-end`): the editor
and the run have the whole file

<div class="run-side">

<<< @/snippets/example.elpi elpi {monaco-run}

</div>

---

# A loop

Run on click only; it stops after 1000000 steps.

```elpi {monaco-run} {autorun:false}
pred loop.
loop :- loop.
main :- print "looping...", loop.
```
