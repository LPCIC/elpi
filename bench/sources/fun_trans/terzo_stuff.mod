module terzo_stuff.

type printterm out_stream -> A -> o.
type readterm in_stream -> A -> o.

printterm Ch X :-
  term_to_string X S,
  output Ch S.

readterm Ch X :-
  input Ch 10000 S,
  string_to_term S X.
