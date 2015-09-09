module main.

import utils.

import poly_typing.
import poly_oper_sem.
import part_eval.
import tp_part_eval.
import termination.
import trafo.
import cse.

type main_aux in_stream -> o.

main1 Name :-
  open_in Name File,
  (
    main_aux File
  ;
    true
  ),
  close_in File.

type line o.
type sline o.

line :- println "---------------------------------------------------------------------------".
sline :- nl, nl, line, nl.

main_aux File :-
  readterm File PT,

  nl, line, nl, !,

  print "Initial program (possibly still polymorphically typed):", nl, nl,
  print_tm PT, sline, !,

  tm_of_ptm PT T,
  print "Program without type declarations:", nl, nl,
  print_tm T, sline, !,

  (
    converges T,
    print "Program terminates: yes", sline, !,

    eval T ET,
    print "Result of evaluated program:", nl, nl,
    print_tm ET
  ;
    print "Program terminates: unknown"
  ),

  sline, !,

  part_eval T PET,
  print "Partially evaluated program:", nl, nl,
  print_tm PET, sline, !,

  elim_cse PET CSE_PET,
  print "PE + common subexpression elimination:", nl, nl,
  print_tm CSE_PET, sline, !,

  unsafe_inline_let CSE_PET CSE_INLPET,
  print "PE + CSE + inlining:", nl, nl,
  print_tm CSE_INLPET, sline, !,

  (
    infer_tp PT TP,
    print "Type of program:", nl, nl,
    print_tp TP, sline, !,

    make_tp_ast PT TP_AST,
    print "Typed abstract syntax tree:", nl, nl,
    write TP_AST, sline, !,

    tp_part_eval TP_AST PE_TP_AST,
    print "Partial evaluation with type maintainance:", nl, nl,
    print_tp_ast PE_TP_AST, sline, !,

    unsafe_inline_tp_let PE_TP_AST INL_PE_TP_AST,
    print "PE + inlining with type maintainance:", nl, nl,
    print_tp_ast INL_PE_TP_AST, sline, !
  ;
    true
  ),

  curry CSE_PET CT,
  print "Curried program:", nl, nl,
  print_tm CT, sline.


