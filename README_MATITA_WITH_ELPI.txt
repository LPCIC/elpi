To use Matita with embedded ELPI

1) build elpi.cmxa with

in elpi/ run "make all" or "make trace"

2) build matita.opt and matitac.opt

in elpi/matita run "make opt"
you may need to run "autoconf" and "./configure" before

3) run a matita script

in elpi/matita/matita/lib/* run "../../matita.opt" or "../../matitac.opt"
on the script, with the options below:

required:
  -elpi <kernel>  the prolog kernel to use: NO, CSC, FG0, FG1

CSC is the ufficial kernel/elaborator for DALEFEST
FG0 and FG1 are experimental kernels/elaborators

optional:
  -elpi-trace  turn on prolog query tracing
  -elpi-quiet  turn off prolog informational prints
  -elpi-cache  turn on prolog query caching

N.B. -elpi-trace only works if elpi.cmxa was built with make trace
For now trace options are hard-coded in
elpi/matita/components/ng_kernel/nCicELPI.ml
inside the function "trace_on"
