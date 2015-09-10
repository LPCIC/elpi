module funs.

type  mapfun   (A -> B) -> list A -> list B -> o.
type  foldr    (A -> B -> B) -> B -> list A -> B -> o.
type  foldl    (A -> B -> A) -> A -> list B -> A -> o.

% Relates a function and two lists if elements of the second list are
% the result of applying (via beta-conversion) the function to the
% corresponding element of the first list.

mapfun F nil nil.
(mapfun F (X :: L) ((F X) :: K)) :- (mapfun F L K).

% "fold" a list to the right.  That is, foldr atoms of the
% following form are provable.
%   foldr F Init (X1 :: X2 :: ... :: Xn :: nil)
%            (F X1 (F X2 (... (F Xn Init)))).

foldr F X nil X.
(foldr F X (W :: L) (F W Y)) :-  (foldr F X L Y).

% "fold" a list to the left.  That is, foldl atoms of the following 
% form are provable.
%   foldl F Init (X1 :: X2 :: ... :: Xn :: nil)
%            (F (F (... (F Init Xn) ... ) X2) X1).

foldl F X nil X.
(foldl F X (W :: L) (F Y W)) :-  (foldl F X L Y).
