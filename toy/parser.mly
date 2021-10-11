%{
    open Ast

    (* The fact:
           Head.
       is equivalent to the rule:
           Head :- true.
    *)
    let fact_sugar p = (p, [], [])

    (* An atom can be regarded as a compound term with arity zero *)
    let atom_sugar a = App (a, [])
%}

/* Refer to:

   https://www.cs.uni-potsdam.de/wv/lehre/Material/Prolog/Eclipse-Doc/userman/node140.html
   https://github.com/simonkrenger/ch.bfh.bti7064.w2013.PrologParser/blob/master/doc/prolog-bnf-grammar.txt

   for a description of the grammar */

/* Tokens */

/* Constants */
%token <string> ATOM

/* Variables */
%token <string> VAR

/* Symbols */
%token RULE       /* :- */
%token CRULE       /* ?- */
%token PIPE       /* | */
%token LTN       /* < */
%token PERIOD     /* .  */
%token LPAREN     /* (  */
%token RPAREN     /* )  */
%token COMMA      /* ,  */

%token EOF

/* Start symbols */
%start clause query program

/* Types */
%type <Ast.tm * (string * string) list * Ast.tm list> clause
%type <(Ast.tm * (string * string) list * Ast.tm list) list> program
%type <Ast.tm> predicate term structure
%type <Ast.tm list> term_list predicate_list query

%%

program:
    | c = clause; EOF              { [c] }
    | c = clause; p = program { c :: p }

clause:
    | p = predicate; PERIOD                             { fact_sugar p }
    | p = predicate; RULE; pl = predicate_list; PERIOD  { (p, [], pl) }
    | p = predicate; CRULE; cl = constraint_list; PIPE; pl = predicate_list; PERIOD  { (p, cl, pl) }

predicate_list:
    | p = predicate                                     { [p] }
    | p = predicate; COMMA; pl = predicate_list         { p :: pl }

constraint_list:
    | c = cst { [c] }
    | c = cst; COMMA; cl = constraint_list    { c :: cl }

cst:
    | c1 = cterm; LTN; c2 = cterm {  (c1,c2) }

query:
    | pl = predicate_list; EOF { pl }

predicate:
    | a = ATOM                                          { atom_sugar a }
    | s = structure                                     { s }

structure:
    | a = ATOM; LPAREN; RPAREN                          { atom_sugar a }
    | a = ATOM; LPAREN; tl = term_list; RPAREN          { App (a, tl) }

term_list:
    | t = term                                          { [t] }
    | t = term; COMMA; tl = term_list                   { t :: tl }

term:
    | a = ATOM                                          { atom_sugar a }
    | v = VAR                                           { atom_sugar v }
    | s = structure                                     { s }

cterm:
    | a = ATOM                                          { a }
    | v = VAR                                           { v }

