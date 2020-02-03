    /* File parser.mly */
    %{
open Ast
            let mkloc i j = (Parsing.rhs_start_pos i, Parsing.rhs_end_pos j)
            let rec mklam = function
              | [] -> fun x -> x
              | (loc,x)::xs -> fun b -> { loc = (fst loc, snd b.loc); v = Lam(x,mklam xs b) }
            let rec mklist loc = function
                    | [] -> { loc; v = Const "[]" }
              | (loc,x) :: xs -> { loc; v = App( { loc; v = App( { loc; v = Const "::" }, x) }, mklist loc xs) }
            %}
        %token <int> INT
        %token <string> IDENT
        %token LET IN LAM ARROW
        %token LPAREN RPAREN EQ LBRK RBRK COMMA SEMICOLON
        %token EOF
        %start main             /* the entry point */
        %type <Ast.ast> main
        %%
        main: term EOF { $1 } ;

        term0:
          | INT                     { { loc = mkloc 1 1;
                                        v = Int $1 }}
          | LPAREN term RPAREN      { $2 }
          | LPAREN term COMMA term RPAREN      
              { { loc = mkloc 1 5; v = App( { loc = mkloc 1 3; v = App({ loc = mkloc 3 3; v = Const "," } ,$2) }, $4 ) } }
          | LBRK term_list RBRK { mklist (mkloc 1 3) $2 }
          | IDENT { { loc = mkloc 1 1; v = Const $1 } }
        ;

        term_list:
          | term SEMICOLON term_list { (mkloc 1 2, $1) :: $3 }
          | term { [(mkloc 1 1, $1)] }
          | { [] }
          ;

        term:
          | LET idlist EQ term IN term { { loc = mkloc 1 6; v = Let(snd (List.hd $2),mklam (List.tl $2) $4,$6) }}
          | LAM IDENT ARROW term { { loc = mkloc 1 4; v = Lam($2,$4) }}
          | term EQ term { { loc = mkloc 1 3; v = Eq($1,$3) } }
          | app { $1 }
          ;
        app:      
          | app term0 { { loc = mkloc 1 2; v = App($1,$2) } }
          | term0 { $1 }
          ;

        idlist:
          | IDENT { [(mkloc 1 1, $1)] }
          | IDENT idlist { (mkloc 1 2, $1) :: $2 }
          ;

        
