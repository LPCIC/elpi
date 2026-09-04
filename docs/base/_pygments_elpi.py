"""A Pygments lexer for the Elpi code in this manual.

Pygments ships an ``ElpiLexer`` but (as of 2.19) it only understands the old
``pred name i:T, o:T.`` signature form and a handful of rule attributes. The
manual uses the current ``pred name In.. -> Out..`` / ``func name In.. -> Out..``
forms and attributes such as ``:functional`` and ``:nooc``. This subclass adds
those; everything else is inherited.
"""

from pygments.lexer import inherit, bygroups, include
from pygments.lexers import ElpiLexer
from pygments.token import Keyword, Name, Text, String

_cs = ElpiLexer.const_sym_re
_const = ElpiLexer.constant_re


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
            # predicate signatures: pred / func / external {pred,func,symbol}
            (rf"\b(external func|external pred|external symbol|func|pred)(\s+)({_cs})",
             bygroups(Keyword.Declaration, Text.Whitespace, Name.Function),
             "elpi-signature"),
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
    }
