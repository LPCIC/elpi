"""A Pygments lexer for the Elpi code in this manual.

Pygments ships an ``ElpiLexer`` but (as of 2.19) it only understands the old
``pred name i:T, o:T.`` signature form and a handful of rule attributes. The
manual uses the current ``pred name In.. -> Out..`` / ``func name In.. -> Out..``
forms, ``symb name ty`` (and the older ``symbol name : ty``), ``data name
A B ..`` (and the older ``kind name type -> type -> ..``), the ``builtin``
spelling of ``external``, and attributes such as ``:functional`` and
``:nooc``. This subclass adds those; everything else is inherited.
"""

from pygments.lexer import inherit, bygroups, include
from pygments.lexers import ElpiLexer
from pygments.token import Keyword, Name, Text, String, Punctuation

_cs = ElpiLexer.const_sym_re
_const = ElpiLexer.constant_re
# "builtin" and "symb" are accepted as alternate spellings of "external" and
# "symbol" respectively (src/parser/lexer.mll.in:
# ("external"|"builtin") / ("symbol"|"symb")) — "builtin"/"symb" are now the
# manual's preferred spelling, "external"/"symbol" the older, still-legal one.
# Colour every combination the same way.
_ext = r"(?:external|builtin)"
_symkw = r"(?:symbol|symb)"


class ElpiManualLexer(ElpiLexer):
    name = "Elpi"
    aliases = ["elpi"]
    filenames = ["*.elpi"]

    tokens = {
        "elpi": [
            # bare rule / signature attributes (no string argument)
            (r"(:functional|:nooc|:untyped|:external)\b", Keyword.Mode),
            # attributes taking a "string" argument
            (r'(:before|:after|:if|:name|:replace|:remove)(\s*)(")',
             bygroups(Keyword.Mode, Text.Whitespace, String.Double),
             "elpi-string"),
            # predicate signatures: pred / func / external (or builtin) {pred,func}
            (rf"\b({_ext} func|{_ext} pred|func|pred)(\s+)({_cs})",
             bygroups(Keyword.Declaration, Text.Whitespace, Name.Function),
             "elpi-signature"),
            # data constructors: `symbol name : ty` / `external symbol name : ty`
            # (the modern spelling of `type name ty`, which the stock lexer
            # already handles — render this the same way, `:` included);
            # `symb` and `builtin` are accepted spellings of `symbol` / `external`
            (rf"\b({_ext} {_symkw}|{_symkw})(\s+)(({_cs}(,\s*)?)+)",
             bygroups(Keyword.Declaration, Text.Whitespace, Name.Function),
             "elpi-symbol-type"),
            # data types: `data name` / `data name A B ..` (one placeholder
            # per parameter, no arrows — unlike `kind`, which the stock lexer
            # already handles); an optional builtin/external prefix is
            # accepted (and ignored) too
            (rf"\b(?:({_ext})(\s+))?(data)(\s+)({_const})",
             bygroups(Keyword.Declaration, Text.Whitespace, Keyword.Declaration,
                      Text.Whitespace, Name.Function),
             "elpi-data-params"),
            # the lambda binder (the stock lexer only handles lowercase `x\`)
            (r"\\", Keyword.Declaration),
            # a bare colon: type ascription `(t : ty)`, sequent `?-` context, ...
            (r":", Punctuation),
            inherit,
        ],
        # a signature body: accepts both `i:T, o:T` and `In.. -> Out..`
        "elpi-signature": [
            (r"(i|o):", Keyword.Mode, "elpi-ctype"),
            (r"->|\.\.", Keyword.Type),
            (r",", Text),
            (r'(ctype\s+)(")', bygroups(Keyword.Type, String.Double),
             "elpi-string"),
            (_const, Keyword.Type),
            (r"[():=]", Keyword.Type),
            (r'"', String.Double, "elpi-string"),
            (r"\.", Text, "#pop"),
            include("_elpi-comment"),
        ],
        # the parameter placeholders (if any) of a `data` declaration, up to
        # the closing `.` — each one is just a name, no arrows or commas
        "elpi-data-params": [
            (_const, Keyword.Type),
            (r"\.", Text, "#pop"),
            include("_elpi-comment"),
        ],
        # the type after `symbol name :` (or `external symbol name :`), up to
        # the closing `.` — same shape as the stock lexer's `elpi-type`, plus
        # the leading `:` and, for the external form, a trailing `= "variant"`
        "elpi-symbol-type": [
            (r":", Punctuation),
            (r"=", Punctuation),
            (r'(ctype\s+)(")', bygroups(Keyword.Type, String.Double),
             "elpi-string"),
            (r"->|\.\.", Keyword.Type),
            (r",", Text),
            (_const, Keyword.Type),
            (r"\(|\)", Keyword.Type),
            (r'"', String.Double, "elpi-string"),
            (r"\.", Text, "#pop"),
            include("_elpi-comment"),
        ],
    }
