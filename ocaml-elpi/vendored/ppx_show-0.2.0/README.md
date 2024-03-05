# OCaml PPX deriver for deriving `show` based on `ppxlib`.

This library reimplements the `show` plugin from [`ppx_deriving`] as a
`ppxlib` deriver.
In particular, this deriver works with OCaml 4.08.0.

[`ppx_deriving`]: https://github.com/ocaml-ppx/ppx_deriving