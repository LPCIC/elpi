" Vim syntax file
" Language:    Lambda Prolog
" Maintainers: Markus Mottl <mottl@miss.wu-wien.ac.at>,
" Last Change: 2000 June 5 - initial release

" Remove any old syntax stuff hanging around.
syn clear

" Lambda Prolog is case sensitive.
syn case match

syn match   lprologBrackErr    "\]"
syn match   lprologParenErr    ")"

syn cluster lprologContained contains=lprologTodo,lprologModuleName,lprologTypeNames,lprologTypeName

" Enclosing delimiters
syn region  lprologEncl transparent matchgroup=lprologKeyword start="(" matchgroup=lprologKeyword end=")" contains=ALLBUT,@lprologContained,lprologParenErr
syn region  lprologEncl transparent matchgroup=lprologKeyword start="\[" matchgroup=lprologKeyword end="\]" contains=ALLBUT,@lprologContained,lprologBrackErr

" General identifiers
syn match   lprologIdentifier  "\<\(\w\|[-+*/\\^<>=`'~?@#$&!_]\)*\>"
syn match   lprologVariable    "\<\(\u\|_\)\(\w\|[-+*/\\^<>=`'~?@#$&!]\)*\>"

syn match   lprologOperator  "/"

" Comments
syn region  lprologComment  start="/\*" end="\*/" contains=lprologComment,lprologTodo
syn region  lprologComment  start="%" end="$" contains=lprologTodo
syn keyword lprologTodo  contained TODO FIXME XXX

syn match   lprologInteger  "\<\d\+\>"
syn match   lprologReal     "\<\(\d\+\)\=\.\d+\>"
syn region  lprologString   start=+"+ skip=+\\\\\|\\"+ end=+"+

" Clause definitions
syn region  lprologClause start="^\w\+" end=":-\|\."

" Modules
syn region  lprologModule matchgroup=lprologKeyword start="^\<module\>" matchgroup=lprologKeyword end="\."

" Types
syn match   lprologKeyword "^\<type\>" skipwhite nextgroup=lprologTypeNames
syn region  lprologTypeNames matchgroup=lprologBraceErr start="\<\w\+\>" matchgroup=lprologKeyword end="\." contained contains=lprologTypeName,lprologOperator
syn match   lprologTypeName "\<\w\+\>" contained

" Keywords
syn keyword lprologKeyword  end import accumulate accum_sig
syn keyword lprologKeyword  local localkind closed sig
syn keyword lprologKeyword  kind exportdef useonly
syn keyword lprologKeyword  infixl infixr infix prefix
syn keyword lprologKeyword  prefixr postfix postfixl

syn keyword lprologSpecial  pi sigma is true fail halt stop not

" Operators
syn match   lprologSpecial ":-"
syn match   lprologSpecial "->"
syn match   lprologSpecial "=>"
syn match   lprologSpecial "\\"
syn match   lprologSpecial "!"

syn match   lprologSpecial ","
syn match   lprologSpecial ";"
syn match   lprologSpecial "&"

syn match   lprologOperator "+"
syn match   lprologOperator "-"
syn match   lprologOperator "*"
syn match   lprologOperator "\~"
syn match   lprologOperator "\^"
syn match   lprologOperator "<"
syn match   lprologOperator ">"
syn match   lprologOperator "=<"
syn match   lprologOperator ">="
syn match   lprologOperator "::"
syn match   lprologOperator "="

syn match   lprologOperator "\."
syn match   lprologOperator ":"
syn match   lprologOperator "|"

syn match   lprologCommentErr  "\*/"

syn sync minlines=50
syn sync maxlines=500

if !exists("did_lprolog_syntax_inits")

  let did_lprolog_syntax_inits = 1

  " The default methods for highlighting.  Can be overridden later

  hi link lprologComment     Comment
  hi link lprologTodo        Todo

  hi link lprologKeyword     Keyword
  hi link lprologSpecial     Special
  hi link lprologOperator    Operator
  hi link lprologIdentifier  Normal

  hi link lprologInteger     Number
  hi link lprologReal        Number
  hi link lprologString      String

  hi link lprologCommentErr  Error
  hi link lprologBrackErr    Error
  hi link lprologParenErr    Error

  hi link lprologModuleName  Special
  hi link lprologTypeName    Identifier

  hi link lprologVariable    Keyword
  hi link lprologAtom        Normal
  hi link lprologClause      Type
endif

let b:current_syntax = "lprolog"

" vim: ts=28
