sig reduce_cbv_nocopy.

kind t type.

type main o.
type app t -> t -> t.
type lam (t -> t) -> t.
type cbv t -> t -> o.
type beta t -> t -> t -> o.
