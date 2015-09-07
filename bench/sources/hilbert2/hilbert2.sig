% version with polymorphic types to prevent eta-expansion

sig hilbert2.
kind  i  type.

%  Notice that there are no constructors for objects in type i.  This
%  allows you to conclude that the only closed terms of 
%                          (i -> i) -> (i -> i) 
%  are the Church numerals.

type  zero, one, church     (A -> (i -> i)) -> o.

type  plus, mult
       ((A -> i -> i) -> (A -> i -> i) ->
        (A -> i -> i)) -> o.

type  succ  ((A -> i -> i) -> (A -> i -> i)) -> o.

type  problem1   (A -> i -> i) ->  (A -> i -> i) -> 
                 (A -> i -> i) ->  (A -> i -> i) -> o.


% added by liang.
type cn int -> ((i -> i) -> (i -> i)) -> o.
type test int -> o.
type go o.

type main o.


