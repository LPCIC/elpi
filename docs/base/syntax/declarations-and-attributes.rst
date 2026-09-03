###########################
Declarations and attributes
###########################

.. note::

   **Stub — part of the manual outline.**

   Planned content: ``kind``; ``type`` (for data constructors and, with ``typeabbrev``, type abbreviations — *not* for predicates); the **signature** forms ``pred name In.. -> Out..`` and ``func name In.. -> Out..`` (a pure relation has no inputs: ``pred name -> Out..``) — this is the one way this manual gives a predicate its signature; ``macro``, ``namespace``, ``shorten``, ``accumulate`` (including string paths), ``constraint`` / ``rule``; the signature and rule attribute catalogue: ``:name``, ``:before``, ``:after``, ``:replace``, ``:remove``, ``:if``, ``:index``, ``:functional``, ``:untyped``, ``:external``; variadic ``..``. The older ``type name … -> prop`` + ``mode`` + ``i:`` / ``o:`` forms, and ``:nooc``, are covered in *Compatibility with Teyjus and Prolog*.

   Source material: ELPI.md; src/builtin.elpi.

   Examples will live in external ``.elpi`` files under ``docs/base/code/`` and be injected with the ``.. elpi::`` directive plus an ``:assert:`` line pinning the printed output.
