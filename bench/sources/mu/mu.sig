sig mu.

kind e type.
kind mylist type -> type.

type xnil mylist e. 
type xcons e -> mylist e -> mylist e. 
type xnil2 mylist (mylist e). 
type xcons2 (mylist e) -> mylist (mylist e) -> mylist (mylist e). 
type s e -> e. 
type zero e. 
type m e. 
type i e. 
type a e.
type u e.  
type once o.
type mu o.
type ge e -> e -> o.
type theorem mylist e -> e -> mylist (mylist e) -> o.
type rule  e -> mylist e -> mylist e -> o.
type rule1 mylist e -> mylist e -> o.
type rule2 mylist e -> mylist e -> o.
type rule3 mylist e -> mylist e -> o.
type rule4 mylist e -> mylist e -> o.
type append mylist e -> mylist e -> mylist e -> o.
type iter e -> o -> o.
type plus e -> e -> e -> o.
type mult e -> e -> e -> o.
type exp e -> e -> e -> o.
type main o.


