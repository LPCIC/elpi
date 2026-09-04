#################
Type declarations
#################

.. note::

   **Stub — part of the manual outline.**

   Planned content: how data types and predicate signatures are declared.
   Data: ``kind`` to introduce a type; ``type`` to declare a data constructor;
   ``typeabbrev`` for type abbreviations. ``type`` is **never** used for a
   predicate. Predicate **signatures**: ``pred name In.. -> Out..`` and
   ``func name In.. -> Out..`` (a pure relation has no inputs:
   ``pred name -> Out..``) — this is the one way this manual gives a predicate
   its signature. Overloading a predicate by repeating its signature; the
   variadic ``..`` marker. Attributes that belong on a signature: ``:index``,
   ``:functional``, ``:untyped``, ``:external``. The older
   ``type name … -> prop`` + ``mode`` + ``i:`` / ``o:`` forms, and ``:nooc``,
   are covered in *Compatibility with Teyjus and Prolog*.

   Terminology: a ``pred`` / ``func`` declaration is a **signature** throughout
   this manual (never "the pred/func declaration" or "the predicate
   declaration").

   Source material: ELPI.md; src/builtin.elpi.

   Examples will live in external ``.elpi`` files under ``docs/base/code/`` and
   be injected with the ``.. elpi::`` directive plus an ``:assert:`` line
   pinning the printed output.
