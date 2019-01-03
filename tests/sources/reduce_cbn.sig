sig reduce_cbn.

kind t type.

type main o.
type app t -> t -> t.
type lam (t -> t) -> t.
type copy t -> t -> o.
type cbn t -> t -> o.
type subst (t -> t) -> t -> t -> o.
