sig base.

accum_sig lists.

kind form, cert type.
kind pair type -> type -> type.
kind map type.

type entry_point  cert -> form -> o.

type map list (pair int form) -> map.
type mapsto int -> form -> o.

type problem  string -> form -> cert -> map -> o.
type resProblem  string -> (list (pair int form)) -> cert -> map -> o.
