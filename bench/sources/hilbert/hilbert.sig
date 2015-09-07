sig hilbert.
kind  i  type.

%  Notice that there are no constructors for objects in type i.  This
%  allows you to conclude that the only closed terms of 
%                          (i -> i) -> (i -> i) 
%  are the Church numerals.

type  zero, one, church     ((i -> i) -> (i -> i)) -> o.

type  plus, mult
       (((i -> i) -> i -> i) -> ((i -> i) -> i -> i) ->
        ((i -> i) -> i -> i)) -> o.
type  succ  (((i -> i) -> i -> i) -> ((i -> i) -> i -> i)) -> o.

type  problem1   ((i -> i) -> i -> i) ->  ((i -> i) -> i -> i) -> 
                 ((i -> i) -> i -> i) ->  ((i -> i) -> i -> i) -> o.


% added by liang.
type cn int -> ((i -> i) -> (i -> i)) -> o.
type test int -> o.
type go o.

type main o.

