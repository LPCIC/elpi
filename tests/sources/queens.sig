% ?- queens(4, Qs).
%   produces
%   Qs = [3,1,4,2] ;
%   Qs = [2,4,1,3]

% queens   +int  -[int]

sig queens.

kind i type.

kind mylist type -> type.
type xnil mylist i.
type xcons i -> mylist i -> mylist i.

type spy o -> o.

type xxx mylist i -> o.
type iter i -> o -> o.
type once o.

type zero i.
type s    i -> i.
type plus i -> i -> i -> o.
type mult i -> i -> i -> o.
type exp i -> i -> i -> o.
type less i -> i -> o.
type neq  i -> i -> o.
type queens i -> (mylist i) -> o.
type queens_aux (mylist i) -> (mylist i) -> (mylist i) -> o.
type range i -> i -> (mylist i) -> o.
type not_attack_aux (mylist i) -> i -> o.
type not_attack (mylist i) -> i -> i -> o.
type select  (mylist i) -> (mylist i) -> i -> o.
type q mylist i -> o.
type main o. 

