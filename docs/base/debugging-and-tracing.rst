#####################
Debugging and tracing
#####################

.. note::

   **Stub — part of the manual outline.**

   Planned content: The tracing facility: ``-trace-on``, the ``run`` / ``select`` / ``assign`` trace points, ``-trace-only``, ``-trace-only-pred``, ``-trace-at``, the counters and ``trace.counter``; ``std.spy`` / ``std.spy!``; ``-print`` / ``-print-ast`` / ``-deps``; ``-no-tc``; the ``:if`` debug-rule idiom with ``-D``; the trace elaborator (``elpi-trace-elaborator``) and the VS Code trace browser.

   Source material: ELPI.md “Tracing facility”; coq-elpi tutorial “Debugging”; src/elpi_trace_elaborator.ml; HDR §3.4.

   Examples will live in external ``.elpi`` files under ``docs/base/code/`` and be injected with the ``.. elpi::`` directive plus an ``:assert:`` line pinning the printed output.
