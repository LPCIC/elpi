sig poly_types.

accum_sig types.

% TYPE SCHEMAS FOR POLYMORPHIC TYPE CHECKING

kind schema type.  % kind of schemas


% SCHEMA CONSTRUCTORS

% Constructor for making types instances of a schema.
type in tp -> schema.

% Constructor for quantifying over schemas.
type all (tp -> schema) -> schema.


% BASIC OPERATIONS ON TYPE SCHEMAS (POLYMORPHIC TYPES)

% [output_ptp +Out +TP] prints polymorphic type [TP] to output stream
% [Out].
type output_ptp out_stream -> tp -> o.

% [print_ptp +TP] prints type polymorphic [TP] to standard output.
type print_ptp tp -> o.
