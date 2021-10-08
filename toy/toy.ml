open Runtime

let () =
  let filters = Trace_ppx_runtime.Runtime.parse_argv (List.tl @@ Array.to_list Sys.argv) in

  let checks = [

  `Check("transitive closure loops instead of fail",
      "
      t(a,b).
      t(a,c).
      t(b,d).
      t(X,Y) :- t(X,Z), t(Z,Y).
      t(X,X).
      ",
    "t(a,X)", 4, ["t(a, b)"; "t(a, c)"; "t(a, d)"; "steps"]);

  `Check("transitive closure loops before producing any solution",
      "
      t(X,Y) :- t(X,Z), t(Z,Y).
      t(X,X).
      t(a,b).
      t(a,c).
      t(b,d).
      ",
    "t(a,X)", 1, ["steps"]);

  `Check("cutting the solution is failure",
      "
      t :- !, fail.
      t.
      ",
    "t", 1, ["no"]);

  `Check("cutting nothing is noop",
      "
      t.
      t :- !, fail.
      ",
    "t", 2, ["t"; "no"]);

  `Check("tail cut kills alternatives",
      "
      t.
      t.
      p :- t, !.
      ",
    "p", 2, ["p"; "no"]);

  `Check("tail cut removed, more solutions",
      "
      t.
      t.
      p :- t.
      ",
    "p", 3, ["p"; "p"; "no"]);

  `Check("table loop",
      "
      _t :- _t.
      ",
    "_t", 1, ["no"]);

  `Check("table next",
    "
    _t(X) :- _t(X).
    _t(a).
    ",
  "_t(X)", 2, ["_t(a)"; "no"]);

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
    "_p(a,Z)", 3, ["_p(a, b)"; "_p(a, c)"; "no"]);

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
    "_p(a,Z)", 3, ["_p(a, b)"; "_p(a, c)"; "no"]);

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
    "_p(a,Z)", 3, ["_p(a, b)"; "_p(a, c)"; "no"]);

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
    "_p(a,Z)", 3, ["_p(a, b)"; "_p(a, c)"; "no"]);

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
    "_p(a,Z)", 1, ["no"]);

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
    "_p(a,Z), x(Z)", 2, ["_p(a, c), x(c)"; "no"]);

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
    "_p(a,Z), x(Z)", 1, ["no"]);

    `Check("fibo",
    "
    f(z).
    f(s(z)).
    f(s(s(X))) :- f(s(X)), f(X).
    ",
    "f(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z)))))))))))))))))", 1, ["steps"]);

    `Check("fibo tab",
    "
    _f(z).
    _f(s(z)).
    _f(s(s(X))) :- _f(s(X)), _f(X).
    ",
    "_f(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z)))))))))))))))))", 1, ["_f(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z)))))))))))))))))"]);

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
    "main(a,a)", 3, ["main(a, a)"; "main(a, a)"; "no"]);

    `Check("table trail hard",
    "
    _p(a,b).
    _p(b,c).
    _p(X,Z) :- _p(X,Y), _p(Y,Z).
    _p(X,X).
    ",
    "_p(a, X)", 4, ["_p(a, b)"; "_p(a, c)"; "_p(a, a)"; "no"]);

    `Check("table cut",
    "
    _p(a,b).
    _p(b,c).
    _p(X,Z) :- _p(X,Y), !, _p(Y,Z).
    _p(X,X).
    ",
    "_p(a, X)", 3, ["_p(a, b)"; "_p(a, c)";"no"]);

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
    "main", 1, ["no"]);

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
    "main", 1, ["steps"]);

    `Check("table open solution",
    "
    _p(a,Y).
    _p(Y,c).
    _p(a,b) :- _p(a,X), _p(X,c).
    ",
    "_p(a, X)", 4, ["_p(a, X0)"; "_p(a, c)"; "_p(a, b)";"no"]);

    `Check("table subsumption",
    "
    _p(X).
    ",
    "_p(X),_p(s(X)),_p(z)", 2, ["_p(X0), _p(s(X0)), _p(z)"; "no"]);


  ] in

  let filter allowed = function
    | `Check(name,_,_,_,_) -> allowed = [] || List.mem name allowed in
  let checks = List.filter (filter filters) checks in
  List.iter check checks;

  exit !errors
;;


