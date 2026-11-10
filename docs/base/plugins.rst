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

For ``elpi`` and ``elpi-lsp`` a package is a findlib package, named as
findlib names it: ``foo.bar`` is the subpackage ``bar`` of ``foo``, and the
directory of ``foo`` is the one that ``ocamlfind query foo`` prints. For
example the package ``elpi-json``, installed by the opam package of the same
name, gives the builtins of its plugin and a file of utilities,
``utils.elpi``:

.. elpi:: code/json.elpi
   :assert: json.list \[json.int 1, json.int 2\]

``elpi`` loads the OCaml code of ``elpi-json`` when it meets ``accumulate
"+elpi-json"`` (the file of utilities accumulates it too: a plugin is
accumulated once).


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
``greet`` is installed, as the findlib package ``greet`` with its
``elpi.toml`` next to its ``META``, so that ``"+/..."`` in its files keeps
naming them (see `Using other packages`_).


Writing a plugin
================

The OCaml side of a plugin calls ``Plugin.register`` when it is loaded, with
the name of its findlib package and a list of declarations, the same as for
``BuiltIn.declare`` (see :doc:`embedding`). This one, from the tests of Elpi,
is the plugin of the findlib package ``elpi-test-dyn``:

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
by ppx_elpi (see :doc:`embedding`), as the ones of ``elpi-json`` are.


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
its ``accumulate`` is an error. Most plugins, ``elpi-json`` among them, declare
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
does. The package ``elpi-json`` generates its stub ``elpi-json.builtins.elpi``
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
   ``.hg``, ``dune-workspace``, ``_RocqProject`` or ``_CoqProject``) and does not look
   in the home directory
   or above it, so that a stray ``~/elpi.toml`` is not the project of every
   file.

Syntax
   A subset of TOML: one ``key = value`` per line (a list can span several
   lines), where the value is a string or a list of strings, and comments
   from ``#`` to the end of the line. The only tables are the sections
   ``[paths]`` and ``[warnings]`` (below), whose keys are on the lines
   after them; a key can be quoted (``"a.b" = ...``). A string is
   written between double quotes, with the escapes of TOML (``\"``,
   ``\\``, ``\n``, ``\t``, ``\uXXXX`` ...), or between single quotes,
   with no escapes (``'C:\dir'``).

Keys
   Each key is given at most once, and only ``name`` is required.

   ``name``
      a string, the findlib name of the package of the project (not empty,
      with no ``/`` nor ``\``), as in ``"+name/..."``: its ``elpi.toml``
      is installed in the directory of that package, which is checked when
      another project uses it and by ``elpi -check-package``
      (`Checking an installed package`_)
   ``use``
      a list of packages, written ``"+pkg"``, whose ``elpi.toml`` (in the
      directory of the package) is used too: their ``[paths]``,
      ``prelude`` and ``preload`` are the ones of the project as well,
      described in `Using other packages`_
   ``[paths]``
      a section: each key is a prefix, and its value a directory or a list
      of directories, as Rocq's ``-Q``. A host application can find the
      accumulated files its own way, with the ``file_resolver`` of
      ``Setup.init``, as Rocq does with its logical paths; ``[paths]``
      replicates that resolver outside the application, so that ``elpi``
      and ``elpi-lsp`` find the same files. ``accumulate "a.b/x"`` reads
      ``x.elpi`` in the directories of the prefix ``a.b`` (written
      ``"a.b" = "+/src/b"``, quoted since it has a dot), in order. The empty
      prefix, ``"" = "+/lib"``, is a directory where any accumulated file is
      searched, after the ones given by ``-I``. ``paths = [...]``, a list,
      is an error
   ``[dev-only-paths]``
      a section like ``[paths]``, used only when ``elpi.toml`` is the one
      of the project being worked on: the nearest one above the file that
      ``elpi`` runs or that ``elpi-lsp`` checks, or the one given with
      ``-config``. It is not used when another project reads ``elpi.toml``
      through ``use``, nor by ``elpi -check-package``, so it can name
      directories that are not installed, such as the tests of the
      project: ``rocq-elpi`` has ``"elpi.tests" = "+/tests"`` there. Its
      prefixes come after the ones of ``[paths]``
   ``prelude``
      a list of strings found as the ones of ``accumulate`` are, e.g.
      ``"+elpi-json/utils"``: their files are given to ``Setup.init`` as
      builtins, so that their macros are seen by every file of the project.
      ``"+pkg"`` is the plugin of ``pkg``, or its stub if the plugin is not
      loaded. A file of the prelude can accumulate other files; a file that
      a program accumulates and that is in the prelude already is not added
      again
   ``preload``
      a list of findlib packages whose plugins are loaded *before*
      ``Setup.init``, and not when a file accumulates them. A plugin can
      declare state components, or quotations that change how the files of
      the project are parsed (``{{ ... }}`` in ``rocq-elpi-lsp-shim``): these
      exist only if the plugin is loaded before the first file is read, so
      such a plugin has to be preloaded. ``elpi-lsp`` loads them too, when
      a document of the project is opened
   ``[warnings]``
      a section: each key is a kind of warnings, and its value ``"off"``
      (the warning is not shown), ``"on"`` (the default) or ``"error"``
      (the warning is an error: ``elpi`` stops, ``elpi-lsp`` shows it as
      an error). The kinds are ``linear-variable``, ``undeclared-global``,
      ``flex-clause``, ``implication-precedence`` and ``nested-accumulate``;
      ``all`` is all of them, and a later key overrides an earlier one. The
      option ``-w SPEC`` of ``elpi`` changes the level of one kind after
      ``elpi.toml``: ``+name`` turns it on, ``-name`` off, and ``@name``
      makes it an error. It is repeated for several kinds, and a later one
      overrides an earlier one, e.g. ``-w -linear-variable -w
      @undeclared-global``

A directory of ``[paths]`` or a file of ``prelude`` is written as in
``accumulate``: ``"+/dir"`` is ``dir`` in the root of the project (the
directory of ``elpi.toml``), ``"+pkg/dir"`` is ``dir`` in the directory of
the package ``pkg`` (``"+pkg"`` is that directory); an absolute path is also
accepted. A relative one, such as ``"lib"``, is an error, so that an
``elpi.toml`` means the same in the sources of a project and where its package
is installed. An unknown key, a duplicate one, or a value of the wrong kind
is an error located at its line of ``elpi.toml``, such as ``elpi.toml: unknown
key plugins (name, use, prelude, preload and the sections [paths],
[dev-only-paths] and [warnings] are)`` on line 3. For example, the project of this test:

.. literalinclude:: ../../tests/plugin/proj/elpi.toml
   :language: toml

has its main file accumulate a file found through ``[paths]`` (``libfile``,
in ``lib``, ``proj.deep/more``, in ``src/deep``, and ``dyn/util``, in the
directory of the package ``elpi-test-dyn``), one found through
``[dev-only-paths]`` (``proj.tests/t``, in ``tests``), a preloaded plugin
and a file of the project, and use a macro of its prelude:

.. literalinclude:: ../../tests/plugin/proj/main.elpi
   :language: elpi


Using other packages
====================

The ``elpi.toml`` of a project is installed with its package, next to its
``META``, and the files that it names are installed where it expects them:
the installed tree mirrors the sources, so that ``"+/..."`` keeps its meaning.
A project that builds on other packages names them in ``use``; their
``elpi.toml`` gives the project their ``[paths]``, their ``prelude`` and their
``preload``, so that it need not repeat how their files accumulate one
another. The packages of ``use`` are followed transitively: the ``[paths]``
of a used package come after the ones of the project, and its ``prelude`` and
``preload`` before; an entry given twice counts once. ``[dev-only-paths]``
and ``[warnings]`` are not used.

A package with no ``elpi.toml``, or whose ``elpi.toml`` has a ``name`` that
is not the findlib name of the package, is an error at the line of ``use``.

For example, the package ``elpi-test-dyn`` of the tests installs this
``elpi.toml``, with the files ``macros.elpi`` and ``lib/double.elpi``:

.. literalinclude:: ../../tests/plugin/ocamlpath/elpi-test-dyn/elpi.toml
   :language: toml

and a project that uses it:

.. literalinclude:: ../../tests/plugin/useproj/elpi.toml
   :language: toml

finds ``lib/double.elpi`` through the prefix ``dyn.lib``, sees the macro of
its prelude, and has its plugin ``elpi-test-dyn.state`` preloaded:

.. literalinclude:: ../../tests/plugin/useproj/main.elpi
   :language: elpi

In the same way the ``elpi.toml`` of ``rocq-elpi`` names the files of its
prelude and the logical paths (``elpi_elpi``, ``elpi.apps.derive.elpi``)
that its files accumulate, and a library written with it, such as Trocq,
has ``use = ["+rocq-elpi"]`` and only its own ``[paths]``.


Checking an installed package
=============================

``elpi -check-package pkg`` checks the package ``pkg`` as findlib finds it
installed, so that a file that was not installed shows up before another
project needs it. It checks:

- its ``elpi.toml``, if it has one, read as ``use`` reads it: its ``name``
  is ``pkg``, and its ``[dev-only-paths]`` are not used;
- its plugin, if it installs a stub ``pkg.builtins.elpi``: the plugin is
  dynlinked and registers under the name ``pkg``, the stub compiles, and
  the stub is the documentation that ``BuiltIn.document_fmt`` prints for
  the plugin, so it is not stale;
- each ``.elpi`` file of its directory (the stubs aside), shown as the
  ``"+pkg/file"`` that accumulates it: the file is parsed and compiled as
  ``elpi-lsp`` compiles a document of a project that uses ``pkg``, with
  the ``preload``, ``prelude`` and ``[paths]`` of its ``elpi.toml``. So
  every file that it accumulates, directly or not, must be installed. A
  file of the prelude is compiled with the prelude, and shown as ``ok (in
  the prelude)``.

It prints one line for each of these items, ``ok`` or the errors, and exits
with 1 if one of them failed. The install of dune, in
``_build/install/default/lib``, has the same layout as the installed
package, so a package can be checked before it is installed:

.. code-block:: sh

   dune build @install
   OCAMLPATH=$PWD/_build/install/default/lib elpi -check-package elpi-test-dyn

For the package ``elpi-test-dyn`` of the tests, whose ``macros.elpi`` is its
prelude, it prints:

.. literalinclude:: ../../tests/plugin/checkdyn.expected
   :language: none


In a host application
=====================

``Setup.init ~packages`` gives Elpi the packages of the host: the directory of
a package, the root of the project that contains a directory (for
``"+/..."``)
and, optionally, a function that loads the OCaml code of a package. Without
it, ``accumulate "+..."`` is an error, but a plugin registered by the host can
still be accumulated. The library ``elpi.dynload`` (module ``Elpi_dynload``)
provides the ones of findlib and of ``elpi.toml``: ``packages`` loads plugins
with dynlink, as ``elpi`` does, ``packages_stubs`` reads their stubs
instead, as ``elpi-lsp`` does; it also reads ``elpi.toml``.
