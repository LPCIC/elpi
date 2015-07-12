sig fast_mu.

kind e type.
kind mylist type -> type.

type xnil mylist e. 
type xcons e -> mylist e -> mylist e. 
type s e -> e. 
type zero e. 
type m e. 
type i e. 
type u e.  
type once o.
type theorem mylist e -> o.
type derive mylist e -> mylist e -> e -> e -> mylist e -> e -> o.
type derive2 mylist e -> mylist e -> e -> e -> e -> mylist e -> e -> o.
type lower_bound e -> e -> e -> o.
type rule_aux mylist e -> mylist e -> e -> e -> e -> e -> e -> o.
type rule mylist e -> mylist e -> e -> e -> e -> e -> e -> e -> e -> mylist e -> mylist e -> o.
type rule1 e -> mylist e -> e.
type length mylist e -> e -> o.
type appendd mylist e -> e -> mylist e -> o.
type rev mylist e -> mylist e -> o.
type iter e -> o -> o.
type sum e -> e -> e -> o.
type mult e -> e -> e -> o.
type diff e -> e -> e -> o.
type pow e -> e -> e -> o.
type leq e -> e -> o.
type smaller e -> e -> o.
type less e -> e -> o.
type shift mylist e -> mylist e -> o.
type is_even e -> o.
type modd e -> e -> e -> o.
type divv e -> e -> e -> o.
type ten2two e -> mylist e -> o.
type ten2two_aux e -> mylist e -> o.
type two2ten mylist e -> e -> o.
type main o.
type once o.
type iter0 e -> o -> o.
type plus0 e -> e -> e -> o.
type mult0 e -> e -> e -> o.
type exp0 e -> e -> e -> o.




