sig lambda3.

kind t type.
kind ty type.
kind a type.

type append (mylist a) -> (mylist a) -> (mylist a) -> o.
type of t -> ty -> o.
type termify (mylist a) -> t -> o.
type impl ty -> ty -> ty.
type appl t -> t -> t.
type lam (t -> t) -> t.
type test t -> o .
type x0 a.
type x1 a.
type x2 a.
type x3 a.
type x4 a.
type x5 a.
type x6 a.
type x7 a.
type x8 a.
type x9 a.
type x10 a.

kind i type.
type zero i.
type s    i -> i.
type plus i -> i -> i -> o.
type mult i -> i -> i -> o.
type exp i -> i -> i -> o.
type iter i -> o -> o.
type once t -> o.
type main o. 

kind mylist type -> type.
type xnil mylist a.
type xcons a -> mylist a -> mylist a.
