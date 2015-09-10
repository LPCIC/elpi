sig lists.

kind  pairty   type -> type -> type.

type  pair     A -> B -> (pairty A B).

exportdef  id       (list A) -> (list A) -> o.
exportdef  memb     A -> (list A) -> o.
exportdef  member   A -> (list A) -> o.
exportdef  append   (list A) -> (list A) -> (list A) -> o.
exportdef  join     (list A) -> (list A) -> (list A) -> o.
exportdef  assoc    A -> B -> (list (pairty A B)) -> o.
exportdef  domain   (list (pairty A B)) -> (list A) -> o.
exportdef  range   (list (pairty A B)) -> (list B) -> o.

