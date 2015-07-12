sig reduce_cbv.

kind t type.

type main o.
type app t -> t -> t.
type lam (t -> t) -> t.
type copy t -> t -> o.
type cbv t -> t -> o.
type beta t -> t -> t -> o.
