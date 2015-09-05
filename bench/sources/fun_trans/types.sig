sig types.

% TYPES OF A SIMPLE FUNCTIONAL LANGUAGE

kind tp type.  % kind of types


% TYPE CONSTRUCTORS

type unit tp.              % unit type
type --> tp -> tp -> tp.   % function type
type **  tp -> tp -> tp.   % product type
type ++  tp -> tp -> tp.   % sum type
type mu (tp -> tp) -> tp.  % recursive type

% Fixity declarations for type constructors.
infixr --> 3.
infixr ++  4.
infixr **  5.


% BASIC OPERATIONS ON TYPES

% [output_tp +Out +TP] prints type [TP] to output stream [Out].
type output_tp out_stream -> tp -> o.

% [print_tp +TP] prints type [TP] to standard output.
type print_tp tp -> o.
