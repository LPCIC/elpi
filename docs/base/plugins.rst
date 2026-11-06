#####################
Plugins and packages
#####################

A *plugin* is the OCaml code of a package that adds builtins to Elpi: an
ordinary OCaml library that registers its builtins when it is loaded. A
program accumulates a plugin, or a file of a package, by naming the package
in the string of an ``accumulate`` directive. The ``elpi`` command loads the
OCaml code of a plugin when a program needs it; the language server
``elpi-lsp`` reads a description of it instead. Writing a host application of
your own, with its builtins given to ``Setup.init``, is described in
:doc:`embedding`.


Naming a package
================

The string of ``accumulate`` names a file as before, unless it starts with
``+``:

.. code-block:: elpi

   accumulate "lib/util".          % the file lib/util.elpi
   accumulate "+foo/bar".          % bar.elpi in the directory of package foo
   accumulate "+foo.bar/baz".      % baz.elpi in the directory of package foo.bar
   accumulate "+foo.bar".          % the plugin of package foo.bar

A package is a findlib package, for ``elpi`` and ``elpi-lsp``; its directory
is the one that ``ocamlfind query`` prints. A string with a ``/`` after the
name of the package names a file in that directory; one with no ``/`` names
the plugin of the package. A file whose name starts with ``+`` is written
``"./+x"``.


Writing a plugin
================

The OCaml side of a plugin calls ``Plugin.register`` when it is loaded, with
the name of its package and a list of declarations, the same as for
``BuiltIn.declare`` (see :doc:`embedding`). This one, from the tests of Elpi,
is the plugin of the package ``elpi-test-dyn``:

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
builtins given to ``Setup.init``.


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
its ``accumulate`` is an error.

.. literalinclude:: ../../tests/plugin/elpi_test_dyn_state.ml
   :language: ocaml


The stub of a plugin
====================

When the OCaml code of a plugin cannot be loaded, as in ``elpi-lsp`` that only
checks programs, ``accumulate "+pkg"`` reads its *stub* instead: the file
``pkg.plugin.elpi`` in the directory of the package. The stub is the
documentation of the plugin, the text that ``BuiltIn.document_fmt`` prints:
its ``builtin func`` signatures have no code, and the type checker accepts
them only when the compilation flag ``builtin_stubs`` is set, as ``elpi-lsp``
does. The package ``elpi-json`` generates its stub when it is built and
installs it next to its ``META``:

.. literalinclude:: ../../elpi-json/dune
   :language: scheme

The program that prints it is one line:

.. literalinclude:: ../../elpi-json/src/gen_stub.ml
   :language: ocaml


The project file
================

``elpi`` reads the file ``elpi.toml`` next to the file it runs; the option
``-config FILE`` names another one, and ``-no-config`` reads none. Its keys,
all optional, are lists of strings:

``paths``
   directories where accumulated files are searched, after the ones of
   ``-I``
``prelude``
   what every program accumulates before its file: the strings of
   ``accumulate``, e.g. ``"+elpi-json/utils"``
``preload``
   the packages whose plugins are loaded before ``Setup.init``

Relative paths are relative to the directory of ``elpi.toml``. For example,
the project of this test:

.. literalinclude:: ../../tests/plugin/proj/elpi.toml
   :language: toml

has its main file accumulate a file found through ``paths`` and a preloaded
plugin, and use a predicate of its prelude:

.. literalinclude:: ../../tests/plugin/proj/main.elpi
   :language: elpi


In a host application
=====================

``Setup.init ~packages`` gives Elpi the packages of the host: the directory of
a package and, optionally, a function that loads its OCaml code. Without it,
``accumulate "+..."`` is an error, but a plugin registered by the host can
still be accumulated. The library ``elpi.dynload`` (module ``Elpi_dynload``)
provides the ones of findlib: ``packages`` loads plugins with dynlink, as
``elpi`` does, ``directories`` only finds them, as ``elpi-lsp`` does; it also
reads ``elpi.toml``.
