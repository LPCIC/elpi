open Runtime

let trail_checks () =
  let h = Heap.init ~constraints:[] in
  let h0 = Heap.checkpoint h in
  let v = ref dummy in
  let x = Ast.App("x",[]) in
  let y = Ast.App("y",[]) in
  Heap.assign h v x;
  let h1 = Heap.checkpoint h in
  Heap.backtrack h h0;
  assert(!v = dummy);
  Heap.assign h v y;
  Heap.backtrack h h1;
  assert(!v = x);
  Heap.backtrack h h0;
  assert(!v = dummy)

let () =
  let filters = Trace_ppx_runtime.Runtime.parse_argv (List.tl @@ Array.to_list Sys.argv) in

  trail_checks ();

  let checks = [

  `Check("transitive closure loops instead of fail",
      "
      t(a,b).
      t(a,c).
      t(b,d).
      t(X,Y) :- t(X,Z), t(Z,Y).
      t(X,X).
      ",
    "t(a,X)", ["t(a, b)"; "t(a, c)"; "t(a, d)"; "steps"]);

  `Check("transitive closure loops before producing any solution",
      "
      t(X,Y) :- t(X,Z), t(Z,Y).
      t(X,X).
      t(a,b).
      t(a,c).
      t(b,d).
      ",
    "t(a,X)", ["steps"]);

  `Check("cutting the solution is failure",
      "
      t :- !, fail.
      t.
      ",
    "t", ["no"]);

  `Check("non-hd cut",
    "
    t :- true, !, fail.
    t.
    true.
    x :- t.
    x.
    ",
  "x", ["x"]);


  `Check("cutting nothing is noop",
      "
      t.
      t :- !, fail.
      ",
    "t", ["t"; "no"]);

  `Check("tail cut kills alternatives",
      "
      t.
      t.
      p :- t, !.
      ",
    "p", ["p"; "no"]);

  `Check("tail cut removed, more solutions",
      "
      t.
      t.
      p :- t.
      ",
    "p", ["p"; "p"; "no"]);

  `Check("cut, XSB 5.2.6 - 1",
    "
    _cut_p(X) :- _cut_q(X), _cut_r.
    _cut_r :- _cut_s.
    _cut_s :- _cut_q(X).
    _cut_q(one).
    _cut_q(two).
    ",
    "_cut_p(one)", ["_cut_p(one)"; "no"]);

  `Check("cut, XSB 5.2.6 - 2",
    "
    _cut_p(X) :- _cut_q(X), _cut_r.
    _cut_r :- _cut_s.
    _cut_s :- _cut_q(X).
    _cut_q(one).
    _cut_q(two).
    ",
    "_cut_p(two)", ["_cut_p(two)"; "no"]);

  `Check("cut, XSB 5.2.6 - 3",
    "
    _cut_p(X) :- _cut_q(X), _cut_r, !.
    _cut_r :- _cut_s.
    _cut_s :- _cut_q(X).
    _cut_q(one).
    _cut_q(two).
    ",
    "_cut_p(one)", ["_cut_p(one)"; "no"]);

  `Check("cut, XSB 5.2.6 - 4",
    "
    _cut_p(X) :- _cut_q(X), _cut_r, !.
    _cut_r :- _cut_s.
    _cut_s :- _cut_q(X).
    _cut_q(one).
    _cut_q(two).
    ",
    "_cut_p(two)", ["_cut_p(two)"; "no"]);

  `Check("cut, XSB 5.2.6 - 5",
    "
    _cut_p(X) :- _cut_q(X), _cut_r, !.
    _cut_r :- _cut_s.
    _cut_s :- _cut_q(X).
    _cut_q(one).
    _cut_q(two).
    ",
    "_cut_p(A)", ["_cut_p(one)"; "no"]); (* XSB gives cut_p(2) ?!?!?! *)

  `Check("cut, XSB 5.2.6 - 6",
    "
    _cut_p(X) :- _cut_q(X), _cut_r, !.
    _cut_r :- _cut_s.
    _cut_s :- _cut_q(X).
    _cut_q(one).
    _cut_q(two).
    ",
    "_cut_p(A), _cut_q(B)", ["_cut_p(one), _cut_q(one)"; "_cut_p(one), _cut_q(two)"; "no"]);

    `Check("cut, XSB 5.2.6 - 7",
    "
    _cut_p(X) :- _cut_q(X), cut_r, !.
    cut_r :- cut_s.
    cut_s :- _cut_q(X).
    _cut_q(one).
    _cut_q(two).
    ",
    "_cut_p(A), _cut_q(B)", ["_cut_p(one), _cut_q(one)"; "_cut_p(one), _cut_q(two)"; "no"]);

  `Check("table loop",
      "
      _t :- _t.
      ",
    "_t", ["no"]);

  `Check("table next",
    "
    _t(X) :- _t(X).
    _t(a).
    ",
  "_t(X)", ["_t(a)"; "no"]);

  `Check("AAMFTESLP",
    "
    _p(X,Z) :- _p(X,Y), _p(Y,Z).
    _p(X,Z) :- e(X,Z), q(Z).
    e(a,b).
    e(a,d).
    e(b,c).
    q(a).
    q(b).
    q(c).
    ",
    "_p(a,Z)", ["_p(a, b)"; "_p(a, c)"; "no"]);

    `Check("AAMFTESLP alts sld",
    "
    _p(X,Z) :- _p(X,Y), _p(Y,Z).
    _p(X,Z) :- e(X,Z).
    e(a,b).
    e(a,d).
    e(b,c).
    e(b,d).
    ",
    "_p(a,Z)", ["_p(a, b)"; "_p(a, c)"; "_p(a, d)"; "no"]);


    `Check("AAMFTESLP nodup",
    "
    _p(X,Z) :- _p(X,Y), _p(Y,Z).
    _p(X,Z) :- e(X,Z), q(Z).
    e(a,b).
    e(a,d).
    e(b,c).
    q(a).
    q(b). q(b).
    q(c).
    ",
    "_p(a,Z)", ["_p(a, b)"; "_p(a, c)"; "no"]);

    `Check("AAMFTESLP trclosure order",
    "
    _p(X,Z) :- e(X,Z), q(Z).
    _p(X,Z) :- _p(X,Y), _p(Y,Z).
    e(a,b).
    e(a,d).
    e(b,c).
    q(a).
    q(b). q(b).
    q(c).
    ",
    "_p(a,Z)", ["_p(a, b)"; "_p(a, c)"; "no"]);

    `Check("slg+sld",
    "
    _p(a,b).
    _p(X,Z) :- _p(X,Y), _p(Y,Z).
    _p(b,c).
    _p(b,d).
    ",
    "_p(a,Z)", ["_p(a, b)"; "_p(a, c)"; "_p(a, d)"; "no"]);

    `Check("AAMFTESLP facts order",
    "
    _p(X,Z) :- e(X,Z), q(Z).
    _p(X,Z) :- _p(X,Y), _p(Y,Z).
    e(a,d).
    e(a,b).
    e(b,c).
    q(a).
    q(b). q(b).
    q(c).
    ",
    "_p(a,Z)", ["_p(a, b)"; "_p(a, c)"; "no"]);

    `Check("AAMFTESLP sld cut",
    "
    _p(X,Z) :- e(X,Z), q(Z).
    _p(X,Z) :- _p(X,Y), _p(Y,Z).
    e(a,d) :- !.
    e(a,b).
    e(b,c).
    q(a).
    q(b). q(b).
    q(c).
    ",
    "_p(a,Z)", ["no"]);

    `Check("AAMFTESLP sld context",
    "
    _p(X,Z) :- e(X,Z), q(Z).
    _p(X,Z) :- _p(X,Y), _p(Y,Z).
    e(a,d).
    e(a,b).
    e(b,c).
    q(a).
    q(b). q(b).
    q(c).
    x(c).
    ",
    "_p(a,Z), x(Z)", ["_p(a, c), x(c)"; "no"]);

    `Check("AAMFTESLP sld context fail",
    "
    _p(X,Z) :- e(X,Z), q(Z).
    _p(X,Z) :- _p(X,Y), _p(Y,Z).
    e(a,d).
    e(a,b).
    e(b,c).
    q(a).
    q(b). q(b).
    q(c).
    x(d).
    ",
    "_p(a,Z), x(Z)", ["no"]);

    `Check("fibo",
    "
    f(z).
    f(s(z)).
    f(s(s(X))) :- f(s(X)), f(X).
    ",
    "f(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z)))))))))))))))))", ["steps"]);

    `Check("fibo tab",
    "
    _f(z).
    _f(s(z)).
    _f(s(s(X))) :- _f(s(X)), _f(X).
    ",
    "_f(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z)))))))))))))))))", ["_f(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z)))))))))))))))))"]);

    `Check("alternatives to root",
    "
    _p(X,Z) :- _p(X,Y), _p(Y,Z).
    _p(X,Z) :- e(X,Z).
    e(a,d).
    e(a,b).
    e(b,c).
    main(X,Y) :-  _p(X,Y).
    main(a,a).
    main(a,a).
    ",
    "main(a,a)", ["main(a, a)"; "main(a, a)"; "no"]);

    `Check("table trail hard",
    "
    _p(a,b).
    _p(b,c).
    _p(X,Z) :- _p(X,Y), _p(Y,Z).
    _p(X,X).
    ",
    "_p(a, X)", ["_p(a, b)"; "_p(a, c)"; "_p(a, a)"; "no"]);

    `Check("table cut",
    "
    _p(a,b).
    _p(b,c).
    _p(X,Z) :- _p(X,Y), !, _p(Y,Z).
    _p(X,X).
    ",
    "_p(a, X)", ["_p(a, b)"; "_p(a, c)";"no"]);

    `Check("table fail",
    "
    _p(a,b).
    _p(b,c).
    _p(c,d).
    _p(d,e).
    _p(X,Z) :- _p(X,Y), _p(Y,Z).
    _p(X,Z) :- _p(X,Y), _p(Y,Z).
    _p(X,X).
    main :- _p(a, q).
    main :- _p(a, q).
    main :- _p(a, q).
    main :- _p(a, q).
    main :- _p(a, q).
    main :- _p(a, q).
    ",
    "main", ["no"]);

    `Check("no table fail",
    "
    p1(a,b).
    p1(b,c).
    p1(c,d).
    p1(d,e).
    p(X,Z) :- p1(X,Y), p(Y,Z).
    p(X,Z) :- p1(X,Y), p(Y,Z).
    p(X,X).
    main :- p(a, q).
    main :- p(a, q).
    main :- p(a, q).
    main :- p(a, q).
    main :- p(a, q).
    main :- p(a, q).
    ",
    "main", ["steps"]);

    `Check("table open solution",
    "
    _p(a,Y).
    _p(Y,c).
    _p(a,b) :- _p(a,X), _p(X,c).
    ",
    "_p(a, X)", ["_p(a, X0)"; "_p(a, c)"; "_p(a, b)";"no"]);

    `Check("table subsumption",
    "
    _p(X).
    ",
    "_p(X),_p(s(X)),_p(z)", ["_p(X0), _p(s(X0)), _p(z)"; "no"]);

    `Check("csts1",
    "
    p(X) ?- X < one | true.
    true.
    ",
    "p(X), p(A)", ["X0 < one, X1 < one| p(X0), p(X1)"; "no"]);

    `Check("csts2",
    "
    p(X,Y) ?- X < Y | true.
    true.
    ",
    "p(X,A), p(A,X)", ["X0 < X1, X1 < X0| p(X0, X1), p(X1, X0)"; "no"]);

    `Check("csts table",
    "
    _p(X,Y) ?- X < Y | true.
    true.
    ",
    "_p(X,A), _p(Y,B)", ["X0 < X1, X2 < X3| _p(X0, X1), _p(X2, X3)"; "no"]);

    `Check("csts table2",
    "
    _p(X,Y) ?- X < Y | true.
    c(X,Y) ?- X < Y | true.
    true.
    ",
    "c(C, D), _p(X,A), _p(Y,B)", ["X0 < X1, X2 < X3, X4 < X5| c(X0, X1), _p(X2, X3), _p(X4, X5)"; "no"]);

    `Check("csts table3",
    "
    _p(X,Y) ?- X < Y | true.
    c(X,Y) ?- X < Y | true.
    true.
    ",
    "c(X, Y), _p(X,A), _p(Y,B)", ["X0 < X1, X0 < X2, X0 < X1, X1 < X3, X1 < X1| c(X0, X1), _p(X0, X2), _p(X1, X3)"; "no"]);

    `Check("csts table3 bis",
    "
    true.
    c(X,Y) ?- X < Y | true.
    _p(X,Y) ?- X < Y | true.
    ",
    "c(X, Y), _p(X,A), _p(Y,B)", ["X0 < X1, X0 < X2, X0 < X1, X1 < X3, X1 < X1| c(X0, X1), _p(X0, X2), _p(X1, X3)"; "no"]);

    `Check("dt unif",
    "
    _p(a,b) :- q.
    q.
    ",
    "_p(X, b), _p(a, Y), _p(A,B)", ["_p(a, b), _p(a, b), _p(a, b)"; "no"]);

    `Check("stamp1",
    "
    p(X,Z) :- e(X,Z).
    p(X,Z) :- p(X,Y), p(Y,Z).
    e(a,b).
    e(b,c).
    ",
    "p(a,Z)", ["p(a, b)"; "p(a, c)"; "steps"]);

    `Check("stamp2",
    "
    p(X,Z) :- p(X,Y), p(Y,Z).
    p(X,Z) :- e(X,Z).
    e(a,b).
    e(b,c).
    ",
    "p(a,Z)", ["steps"]);

    `Check("stamp3",
    "
    _p(X,Z) :- _p(X,Y), _p(Y,Z).
    _p(X,Z) :- e(X,Z).
    e(a,b).
    e(b,c).
    ",
    "_p(a,Z)", ["_p(a, b)"; "_p(a, c)"; "no"]);

    `Check("stamp4",
    "
    _p(X,Z) :- _p(X,Y), !, _p(Y,Z).
    _p(X,Z) :- e(X,Z).
    e(a,b).
    e(b,c).
    ",
    "_p(a,Z)", ["no"]);


  ] in

  let filter allowed = function
    | `Check(name,_,_,_) -> allowed = [] || List.mem name allowed in
  let checks = List.filter (filter filters) checks in
  List.iter check checks;

  exit !errors
;;


