#####################
Plugins and packages
#####################

A *package* is a directory of Elpi files, found by name, and a *plugin* is
the OCaml code of a package that adds builtins to Elpi: an ordinary OCaml
library that registers its builtins when it is loaded. A program accumulates
a plugin, or a file of a package, by naming the package in the string of an
``accumulate`` directive. The ``elpi`` command loads the OCaml code of a
plugin when a program needs it; the language server ``elpi-lsp`` reads a
description of it instead. Writing a host application of your own, with its
builtins given to ``Setup.init``, is described in :doc:`embedding`.


Naming a package
================

The string of ``accumulate`` names a file as before, unless it starts with
``+``:

.. code-block:: elpi

   accumulate "lib/util".          % the file lib/util.elpi
   accumulate "+foo/bar".          % bar.elpi in the directory of package foo
   accumulate "+foo.bar/baz".      % baz.elpi in the directory of package foo.bar
   accumulate "+/lib/util".        % lib/util.elpi in the root of the current project
   accumulate "+foo.bar".          % the plugin of package foo.bar

A string with a ``/`` after the name of the package names a file in the
directory of the package; one with no ``/`` names the plugin of the package.
With no name, as in ``"+/lib/util"``, the file is in the root of the
*current* project: the project of the file that contains the ``accumulate``
(see `Projects`_). A file whose name starts with ``+`` is written
``"./+x"``. The older spelling
with no quotes, ``accumulate lib/util.``, is the same as ``accumulate
"lib/util".`` and stays available.

For ``elpi`` and ``elpi-lsp`` the Elpi package ``foo`` is the findlib package
``elpi-foo``, and ``foo.bar`` is ``elpi-foo.bar``: the directory of the
package is the one that ``ocamlfind query elpi-foo`` prints. For example the
package ``json``, installed by the opam package ``elpi-json``, gives the
builtins of the plugin ``json`` and a file of utilities, ``utils.elpi``:

.. elpi:: code/json.elpi
   :assert: json.list \[json.int 1, json.int 2\]

``elpi`` loads the OCaml code of ``json`` when it meets ``accumulate "+json"``
(the file of utilities accumulates it too: a plugin is accumulated once).


Projects
========

A *project* is a package being written: a directory with a file
``elpi.toml`` at its root, which usually gives the name of the package. The
files of the project accumulate one another with ``"+/path"``, the path
being relative to the root, so a file in a subdirectory needs no ``../``:

.. code-block:: text

   greet/
     elpi.toml         name = "greet"
     lib/names.elpi
     src/main.elpi     accumulate "+/lib/names".

.. literalinclude:: code/project/elpi.toml
   :language: toml

.. elpi:: code/project/src/main.elpi
   :assert: hello Alice\nhello Bob

The root of the current project of a file is the directory of the nearest
``elpi.toml`` in its directory or above it (the search is described in `The
project file`_); ``"+/path"`` in a file with no such ``elpi.toml`` is an
error. The project that ``elpi`` runs, or that ``elpi-lsp`` checks, is found
by its name in its root, not among the installed packages:
``"+greet/lib/names"`` is the same file as ``"+/lib/names"`` there. Another
project accumulates the files of ``greet`` as ``"+greet/..."`` once
``greet`` is installed, as the findlib package ``elpi-greet`` with its
``elpi.toml`` next to its ``META``, so that ``"+/..."`` in its files keeps
naming them.


Writing a plugin
================

The OCaml side of a plugin calls ``Plugin.register`` when it is loaded, with
the name of its package and a list of declarations, the same as for
``BuiltIn.declare`` (see :doc:`embedding`). This one, from the tests of Elpi,
is the plugin ``test-dyn``, of the findlib package ``elpi-test-dyn``:

.. literalinclude:: ../../tests/plugin/elpi_test_dyn.ml
   :language: ocaml

A library of dune with a ``public_name`` is a findlib package, and dune
builds the ``.cmxs`` that ``elpi`` loads:

.. code-block:: scheme

   (library
    (name elpi_test_dyn)
    (public_name elpi-test-dyn)
    (libraries elpi))

A program uses its builtins once it accumulates it, here with a file of the
same package:

.. literalinclude:: ../../tests/plugin/main.elpi
   :language: elpi

The plugin is compiled as a unit of its own, like any accumulated file, and
its data types and global symbols are bound to the OCaml ones as for the
builtins given to ``Setup.init``. The data types of a plugin can be derived
by ppx_elpi (see :doc:`embedding`), as the ones of ``json`` are.


Loading a plugin
================

``elpi`` dynlinks the package of a plugin when it meets its ``accumulate``,
if the plugin is not registered yet: loaded before (a package can be linked
in a host application, or loaded by Rocq's ``Declare ML Module``) or later,
a plugin works the same way. The one exception: a plugin loaded after
``Setup.init`` cannot declare state components (``State.declare_component``)
nor quotations, since an instance of Elpi does not see the ones declared after
it was created. Such a plugin, like this one, must be loaded before
``Setup.init``, by the ``preload`` key of ``elpi.toml`` (below); otherwise
its ``accumulate`` is an error. Most plugins, ``json`` among them, declare
neither and need no ``preload``.

.. literalinclude:: ../../tests/plugin/elpi_test_dyn_state.ml
   :language: ocaml


The stub of a plugin
====================

When the OCaml code of a plugin cannot be loaded, as in ``elpi-lsp`` that only
checks programs, ``accumulate "+pkg"`` reads its *stub* instead: the file
``pkg.builtins.elpi`` in the directory of the package. The stub is the
documentation of the plugin, the text that ``BuiltIn.document_fmt`` prints:
its ``builtin func`` signatures have no code, and the type checker accepts
them only when the compilation flag ``builtin_stubs`` is set, as ``elpi-lsp``
does. The package ``elpi-json`` generates its stub ``json.builtins.elpi``
when it is built and installs it next to its ``META``, with its
``elpi.toml``:

.. literalinclude:: ../../elpi-json/dune
   :language: scheme

The program that prints it is one line:

.. literalinclude:: ../../elpi-json/src/gen_stub.ml
   :language: ocaml


The project file
================

``elpi.toml`` is read by ``elpi``, by ``elpi-lsp`` and by the library
``elpi.dynload`` (below).

Location
   ``elpi`` reads the nearest ``elpi.toml`` in the directory of the file it
   runs or above it. The option ``-config FILE`` names another file, and
   ``-no-config`` reads none. ``elpi-lsp`` reads the nearest one above a
   document when the document is opened, and again when it is opened after
   ``elpi.toml`` changed; an error in it is shown at the start of the
   document. The nearest ``elpi.toml`` above an accumulated file is also
   found when that file accumulates ``"+/..."``, whatever the options. The
   search stops at the root of a repository (a directory with ``.git``,
   ``.hg``, ``_darcs`` or ``.jj``) and does not look in the home directory
   or above it, so that a stray ``~/elpi.toml`` is not the project of every
   file.

Syntax
   A subset of TOML: one ``key = value`` per line (a list can span several
   lines), where the value is a string or a list of strings, and comments
   from ``#`` to the end of the line. There are no tables. A string is
   written between double quotes, with the escapes of TOML (``\"``,
   ``\\``, ``\n``, ``\t``, ``\uXXXX`` ...), or between single quotes,
   with no escapes (``'C:\dir'``).

Keys
   All keys are optional, and each key is given at most once.

   ``name``
      a string, the name of the package of the project (not empty, with no
      ``/`` nor ``\``)
   ``paths``
      a list of directories, where accumulated files are searched after the
      ones given by ``-I``
   ``prelude``
      a list of strings of ``accumulate``, e.g. ``"+json/utils"``,
      accumulated before the file that ``elpi`` runs
   ``preload``
      a list of packages whose plugins are loaded before ``Setup.init``,
      needed only by the plugins that declare state components or
      quotations; ``elpi-lsp`` ignores it, since it loads no plugin

Relative paths, in ``paths`` and ``prelude``, are relative to the directory of
``elpi.toml``. An unknown key, a duplicate one, or a value of the wrong kind
is an error that gives the file and the line, such as ``elpi.toml:3: unknown
key plugins (name, paths, prelude and preload are)``. For example, the
project of this test:

.. literalinclude:: ../../tests/plugin/proj/elpi.toml
   :language: toml

has its main file accumulate a file found through ``paths``, a preloaded
plugin and a file of the project, and use a predicate of its prelude:

.. literalinclude:: ../../tests/plugin/proj/main.elpi
   :language: elpi


In a host application
=====================

``Setup.init ~packages`` gives Elpi the packages of the host: the directory of
a package, the root of the project that contains a directory (for
``"+/..."``)
and, optionally, a function that loads the OCaml code of a package. Without
it, ``accumulate "+..."`` is an error, but a plugin registered by the host can
still be accumulated. The library ``elpi.dynload`` (module ``Elpi_dynload``)
provides the ones of findlib and of ``elpi.toml``: ``packages`` loads plugins
with dynlink, as ``elpi`` does, ``directories`` only finds them, as
``elpi-lsp`` does; it also reads ``elpi.toml``.
