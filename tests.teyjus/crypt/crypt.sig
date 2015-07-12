sig crypt.

kind i type.
kind mylist type -> type.

type null i.
type s i -> i.
type xnil mylist i.
type xcons i -> mylist i -> mylist i.
type crypt mylist i -> o.
type sum2 mylist i -> mylist i -> mylist i -> o.
type sum2_aux mylist i -> mylist i -> i -> mylist i -> o.
type mult mylist i -> i -> mylist i -> o.
type mult_aux mylist i -> i -> i -> mylist i -> o.
type plus i -> i -> i -> o.
type prod i -> i -> i -> o.
type divv i -> i -> i -> o.
type modd i -> i -> i -> o.
type less i -> i -> o.
type zero mylist i -> o.
type is_even i -> o.
type is_odd i -> o.
type is_lefteven i -> o.
type digit i -> o.
type even i -> o.
type odd i -> o.
type lefteven i -> o.
type main o.
type once o.
type iter i -> o.
type exp i -> i -> i -> o.
type check mylist i -> mylist i -> o.
