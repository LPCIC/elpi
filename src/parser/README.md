This parser is a standard LR parser based on [Menhir](http://gallium.inria.fr/~fpottier/menhir/).

Tokens, token families and their precedence is described in
[lexer_config.ml](lexer_config.ml). Out of that we generate:
- `lexer.mll` filling in a [template](lexer.mll.in) which contains all other
  lexical convention
- [token_precedence.mly](token_precedence.mly) which is coalesced by Menhir
  with [tokens.mly](tokens.mly) and [grammar.mly](grammar.mly) in order to
  build the LR parser

The file [parse.ml](parse.ml) ties the recursion knot: `accumulate` calls the
parser itself on another *file*. The parser needs to be abstracted
(via an OCaml functor) over a file resolver, this is also done here. Finally
this file holds a cache of already parsed files to preserve the old semantics.
It also loads signature files when loading `.mod` files, for backward
compatibility with Teyjus. The module type `Parser` is defined in
[parse.mli](parse.mli), and is all that clients should use.

The [error messages](error_messages.txt) are maintained by a few
targets in the root `Makefile` starting with `menhir-`, mainly
`menhir-complete-errormsgs` and `menhir-strip-errormsgs`.

Unit tests:
- [test_lexer.ml](test_lexer.ml) tests some lexing rules
- [test_parser.ml](test_parser.ml) tests some parsing rules

While the grammar is not extensible token families provide
an open ended set of mixfix symbols. The relative precedence of a mixfix
is given by its family which is identified by its prefix.

When this parser encounters an mixfix declaration it outputs an error along
these lines:
```
Mixfix directives are not supported by this parser.

The parser is based on token families.
A family is identified by some starting characters, for example
a token '+-->' belongs to the family of '+'. There is no need
to declare it.

All the tokens of a family are parsed with the same precedence and
associativity, for example 'x +--> y *--> z' is parsed as
'x +--> (y *--> z)' since the family of '*' has higher precedence
than the family of '+'.

Here the table of tokens and token families.
Token families are represented by the start symbols followed by '..'.
Tokens of families marked with [*] cannot end with the starting symbol,
eg `foo` is not an infix, while `foo is.
The listing is ordered by increasing precedence.

fixity                     | tokens / token families
-------------------------- + -----------------------------------
Infix   not   associative  | :-  ?-  
Infix   right associative  | ;  
Infix   right associative  | ,  
Infix   right associative  | ->  
Infix   right associative  | =>  
Infix   not   associative  | =  ==  =<  r<  i<  s<  r=<  i=<  s=< 
                             <..  r>  i>  s>  r>=  i>=  s>=  >.. 
                             is  
Infix   right associative  | ::  
Infix   not   associative  | '.. [*]  
Infix   left  associative  | ^..  r+  i+  s+  +..  -  r-  i-  s-  
Infix   left  associative  | r*  i*  s*  *..  /  div  mod  
Infix   right associative  | --..  
Infix   not   associative  | `.. [*]  
Infix   right associative  | ==..  
Infix   right associative  | ||..  
Infix   right associative  | &&..  
Infix   left  associative  | #..  
Prefix  not   associative  | r~  i~  ~..  
Postfix not   associative  | ?..  

If the token is a valid mixfix, and you want the file to stay compatible
with Teyjus, you can ask Elpi to skip the directive. Eg:

% elpi:skip 2  // skips the next two lines
infixr ==> 120.
infixr || 120.

As a debugging facility one can ask Elpi to print the AST in order to
verify how the text was parsed. Eg:

echo 'X = a || b ==> c' | elpi -parse-term
```
