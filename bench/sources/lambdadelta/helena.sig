sig helena.

kind k type. % sort
kind l type. % layer
kind t type. % term
kind g type. % global environment
kind s type. % RTM stack
kind m type. % RTM mode
kind e type. % environment side

type l+0 l.
type l+1 l.
type l+2 l.
type l+y l.

type m+0 m.
type m+1 m.
type m+y m.

type e+sn e.
type e+dx e.

type sort k -> t.
type abbr t -> (t -> t) -> t.
type abst l -> t -> (t -> t) -> t.
type prod l -> t -> (t -> t) -> t.
type appr t -> t -> t.
type appx t -> t -> t.
type cast t -> t -> t.

type gtop g.
type genv int -> g.
type gdef+1 int -> t -> (t -> g) -> g.
type gdec+1 int -> t -> (t -> g) -> g.
type gdef+2 t -> g -> g.
type gdec+2 t -> g -> g.

type satom s.
type scons s -> t -> s.

type m+pred m -> m -> o.
type k+succ k -> k -> o.
type l+zero l -> o.
type l+pred l -> l -> o.

type s+iso  s -> s -> o.
type r+exp  t -> m -> int -> e -> m -> t -> o.
type rtm+0  t -> s -> m -> m -> s -> t -> o.
type conv+  t -> s -> m -> m -> s -> t -> o.
type conv+l t -> s -> m -> m -> s -> t -> o.
type conv+r t -> s -> m -> m -> s -> t -> o.
type conv+s s -> s -> o.
type conv+0 t -> s -> m -> m -> s -> t -> o.
type ok+l   int -> m -> m -> m -> t -> o.
type appl+  t -> s -> m -> t -> o.
type tv+    t -> o.
type gv+    g -> o.
type g+line t -> int -> t -> o.
type g+list int -> g -> o.
type gv+3   t -> o.
