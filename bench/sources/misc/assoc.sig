sig  assoc.

kind pair   type -> type -> type.

type pair   A -> B -> (pair A B).

exportdef assoc  A -> B -> (list (pair A B)) -> o.

