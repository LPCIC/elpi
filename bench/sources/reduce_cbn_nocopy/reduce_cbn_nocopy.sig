sig reduce_cbn_nocopy.

kind t type.

type main o.
type app t -> t -> t.
type lam (t -> t) -> t.
type cbn t -> t -> o.
type subst (t -> t) -> t -> t -> o.
