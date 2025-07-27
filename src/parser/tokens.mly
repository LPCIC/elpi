%token FULLSTOP
%token < string > CONSTANT
%token VDASH
%token QDASH
%token < int > INTEGER
%token < float > FLOAT
%token < string > STRING
%token FRESHUV
%token CUT
%token COLON
%token RTRI
%token BIND
%token LPAREN
%token RPAREN
%token LBRACKET
%token RBRACKET
%token LCURLY
%token RCURLY
%token PIPE
%token AS
%token IS
%token <char> IO_COLON
%token <char> IO
%token ARROW
%token DARROW
%token DDARROW
%token DDARROWBANG
%token DIV
%token MOD
%token < int * string > QUOTED
%token SHORTEN
%token ACCUMULATE
%token LOCAL
%token PRED
%token FUNC
%token MINUS
%token MINUSr
%token MINUSi
%token MINUSs
%token MACRO
%token RULE
%token NAMESPACE
%token CONSTRAINT
%token KIND
%token TYPE
%token TYPEABBREV
%token EXTERNAL
%token MODULE
%token SIG
%token SYMBOL
%token IMPORT
%token ACCUM_SIG
%token USE_SIG
%token LOCALKIND
%token USEONLY
%token EXPORTDEF
%token CLOSED
%token <string> FIXITY
%token PI
%token SIGMA
%token IF
%token BEFORE
%token AFTER
%token UNTYPED
%token FUNCTIONAL
%token REPLACE
%token REMOVE
%token NAME 
%token INDEX 
%token CONS
%token CONJ
%token CONJ2
%token OR
%token EQ
%token EQ2
%token IFF
%token NIL
%token EOF
%token DOTS

%token <string> FAMILY_PLUS
%token <string> FAMILY_TIMES
%token <string> FAMILY_MINUS
%token <string> FAMILY_EXP
%token <string> FAMILY_LT
%token <string> FAMILY_GT
%token <string> FAMILY_EQ
%token <string> FAMILY_QMARK
%token <string> FAMILY_BTICK
%token <string> FAMILY_TICK
%token <string> FAMILY_SHARP
%token <string> FAMILY_TILDE
%token <string> FAMILY_AND
%token <string> FAMILY_OR
%token SLASH

%%
