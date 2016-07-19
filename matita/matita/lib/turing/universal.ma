include "turing/turing.ma".

(* 
Simboli:
0 1 *0 *1 # | ,

[lista di simboli] fa match su un simbolo qualunque nella lista
ad esempio [#|,] fa match con la gratella "#", la barra verticale "|" e la virgola ","

Convenzione variabili:
- x,y,z,D     = bit (non marcati)
- *x,*y,*z,*D = bit marcati
- c,d,e = caratteri (bit marcati e non marcati e separatori)

Convenzioni mosse:
c/D --> Q : leggo c, scrivo c, mi sposto a D e passo allo stato Q
c/d/D --> Q : leggo c, scrivo d, mi sposto a D e passo allo stato Q

MACCHINA per confronto tuple:
=============================
Input:
      *               *
 ls # current # ... | input , output , D | ... # rs
    ^
    0

Output:

 ls # current # ... | input , output , D | ... # rs  (rimuove le marcature e si sposta sull'output)
                              ^
                           SUCCESS

      *                                    *
 ls # current # ... | input , output , D | ... # rs (sposta la marcatura alla tupla successiva)
    ^
 FAILURE

STATO 0:
  #/R --> 1
  
STATO 1:
  \forall c != *z. c/L --> 1
  \forall x. *x/x/R --> 2(x)

STATO 2(x):
  \forall y. y/*y/R --> 3(x)
  #/R --> 3(x)

STATO 3(x):
  \forall y.\forall c != *y. c/R --> 3(x)
  *x/x/R --> 4
  *~x/~x/R --> 5

STATO 4:
  \forall x. x/*x/L --> 1
  ,/R --> SUCCESS
  
STATO 5:
  \forall c != |. c/R --> 5
  |/R --> 6

STATO 6:
  \forall x. x/*x/L --> 7

STATO 7:
  \forall c != #. c/L --> 7
  #/L -→ 8

STATO 8:
  \forall c != #. c/L --> 8
  \forall x. *x/x/L --> 8
  #/R --> 9

STATO 9:
  \forall x. x/*x/L --> FAILURE

*)

inductive alpha_uni : Type[0] ≝ 
| bit : bool → alpha_uni
| mark : bool → alpha_uni
| grid : alpha_uni | bar : alpha_uni | comma : alpha_uni.

inductive Qmatch : Type[0] ≝
| qm0 : Qmatch | qm1 : Qmatch | qm2 : bool → Qmatch | qm3 : bool → Qmatch
| qm4 : Qmatch | qm5 : Qmatch | qm6 : Qmatch | qm7 : Qmatch 
| qm8 : Qmatch | qm9 : Qmatch 
| qmsuccess : Qmatch | qmfailure : Qmatch | qmsink : Qmatch.

definition bool_eqb ≝ λb1,b2:bool.¬ (xorb b1 b2).

definition tmatch ≝ λs,c.
match s with
[ qm0 ⇒ match c with
  [ grid ⇒ 〈qm1,〈grid,R〉〉
  | _ ⇒ 〈qmsink,〈c,N〉〉 ]
| qm1 ⇒ match c with
  [ mark x ⇒ 〈qm2 x,〈bit x,R〉〉
  | _ ⇒ 〈qm1,〈c,L〉〉 ]
| qm2 x ⇒ match c with
  [ bit y ⇒ 〈qm3 x,〈mark y,R〉〉
  | grid ⇒ 〈qm3 x,〈grid,R〉〉
  | _ ⇒ 〈qmsink,〈c,N〉〉 ]
| qm3 x ⇒ match c with
  [ mark y ⇒ match bool_eqb x y with
    [ true ⇒ 〈qm4,〈bit y,R〉〉
    | false ⇒ 〈qm5,〈bit y,R〉〉 ]
  | _ ⇒ 〈qm3 x,〈c,R〉〉 ]
| qm4 ⇒ match c with
  [ comma ⇒ 〈qmsuccess,〈comma,R〉〉
  | bit x ⇒ 〈qm1,〈mark x,L〉〉
  | _ ⇒ 〈qmsink,〈c,N〉〉 ]
| qm5 ⇒ match c with
  [ bar ⇒ 〈qm6,〈bar,R〉〉
  | _ ⇒ 〈qm5,〈c,R〉〉 ]
| qm6 ⇒ match c with 
  [ bit x ⇒ 〈qm7,〈mark x,L〉〉
  | _ ⇒ 〈qmsink,〈c,N〉〉 ]
| qm7 ⇒ match c with
  [ grid ⇒ 〈qm8,〈grid,L〉〉
  | _ ⇒ 〈qm7,〈c,L〉〉 ]
| qm8 ⇒ match c with
  [ grid ⇒ 〈qm9,〈grid,R〉〉 
  | mark x ⇒ 〈qm8,〈bit x,L〉〉 
  | _ ⇒ 〈qm8,〈c,L〉〉 ]
| qm9 ⇒ match c with
  [ bit x ⇒ 〈qmfailure,〈mark x,L〉〉 
  | _ ⇒ 〈qmsink,〈c,N〉〉 ]
| qmsink ⇒ 〈qmsink,〈c,N〉〉 
| qmsuccess ⇒ 〈qmsuccess,〈c,N〉〉
| qmfailure ⇒ 〈qmfailure,〈c,N〉〉].

  
(*
==============================
MACCHINA PER COPIA NUOVO STATO IN CURRENT
==============================

Input:
  
  ls # current # ... | in_state , out_state , D | ... # rs
                                  ^
                                  0

Output:
  ls # out_state # ... | in_state , out_state , D | ... # rs
                                              ^
                                              9

STATO 0:
  \forall x. x/*x/L --> 1
  
STATO 1:
  [01,|]/L --> 1
  #/L --> 2

STATO 2:
  [01]/L --> 2
  #/R -> 3

STATO 3:
  \forall x. x/*x/R --> 4
  #/R --> 8

STATO 4:
  [01,|#]/R --> 4
  \forall x. *x/x/R --> 5(x)

STATO 5(x):
  #/R --> 6(x)
  \forall y. y/*y/L --> 7(x)

STATO 6(x):
  \forall D. D/*D/L --> 7(x)

STATO 7(x):
  [01,|#]/l --> 7(x)
  \forall y. *y/x/R --> 3

STATO 8:
  [01,|#]/R --> 8
  \forall D. *D/D/L --> 9

STATO 9:
  stato finale
*)
(* TODO
match s with
 [ q0 ⇒ match c with
   [ bit x ⇒ 〈q1,〈mark x,L〉〉
   | _ ⇒ 〈qsink,〈c,N〉〉 ]
 | q1 ⇒ match c with
   [ bit x ⇒ 〈q1,〈c,L〉〉
   | comma ⇒ 〈q1,〈c,L〉〉
   | bar ⇒ 〈q1,〈c,L〉〉
   | grid ⇒ 〈q2,〈c,R〉〉
   | _ ⇒ 〈qsink,〈c,N〉〉 ]
 | q2 ⇒ match c with
   [ bit x ⇒ 〈q2,〈c,L〉〉
   | grid ⇒ 〈q3,〈c,R〉〉 
   | _ ⇒ 〈qsink,〈c,N〉〉 ]
 | q3 ⇒ match c with
   [ bit x ⇒ 〈q4,〈mark x,R〉〉
   | grid ⇒ 〈q8,〈c,R〉〉
   | _ ⇒ 〈qsink,〈c,N〉〉 ]
 | q4 ⇒ match c with
   [ bit x ⇒ 〈q4,〈c,R〉〉
   | comma ⇒ 〈q4,〈c,R〉〉
   | bar ⇒ 〈q4,〈c,R〉〉
   | grid ⇒ 〈q4,〈c,R〉〉
   | mark x ⇒ 〈q5 x,〈bit x,R〉〉 ]
 | q5 x ⇒ match c with
   [ grid ⇒ 〈q6 x,〈c,R〉〉
   | bit y ⇒ 〈q7 x,〈mark y,L〉〉
   | _ ⇒ 〈qsink,〈c,N〉〉 ]
 | q6 x ⇒ match c with
   [ bit D ⇒ 〈q7 x,〈mark D,L〉〉
   | _ ⇒ 〈qsink,〈c,N〉〉 ]
 | q7 x ⇒ match c with
   [ bit y ⇒ 〈q7 x,〈c,L〉〉
   | comma ⇒ 〈q7 x,〈c,L〉〉
   | bar ⇒ 〈q7 x,〈c,L〉〉
   | grid ⇒ 〈q7 x,〈c,L〉〉
   | mark y ⇒ 〈q3,〈bit x,R〉〉 ]
 | q8 ⇒ match c with
   [ bit y ⇒ 〈q8,〈c,R〉〉
   | comma ⇒ 〈q8,〈c,R〉〉
   | bar ⇒ 〈q8,〈c,R〉〉
   | grid ⇒ 〈q8,〈c,R〉〉
   | mark D ⇒ 〈q9,〈bit D,L〉〉 ]
 | q9 ⇒ ? (* successo *)
 ].
*)
(*
==================================
MACCHINE PER SPOSTARE LA "TESTINA"
================================

Lo spostamento a sx si ottiene mediante

ls x # current y # macchina # rs
----C--->
ls x # current # y macchina # rs
----B--->
ls x # current # macchina # y rs
----B--->
ls # x current # macchina # y rs
----C--->
ls # current x # macchina # y rs


Lo spostamento a dx si ottiene mediante

ls # current x # macchina # y rs
----A--->
ls x # current # macchina # y rs
----A--->
ls x # current # macchina y # rs
----A--->
ls x # current y # macchina # rs


MACCHINA A
----------
Sposta il carattere binario su cui si trova la testina oltre il primo # alla sua sinistra.

Input:
  
  ls # cs x rs
          ^
          0

Output:
  ls x # cs rs
     ^
     4

STATO 0:
  \forall x.x/L --> 1(x)

STATO 1(x):
  \forall c != #. c/x/R --> 2(c)
  #/x/R --> 3

STATO 2(c):
  \forall d. d/c/L --> 0

STATO 3:
  \forall c. c/#/L --> 4

STATO 4:
  stato finale
*)
(* TODO
match s with
 [ q0 ⇒ match c with
   [ bit x ⇒ 〈q1 x,〈c,L〉〉
   | _ ⇒ 〈qsink,〈c,N〉〉 ]
 | q1 x ⇒ match c with
   [ grid ⇒ 〈q3,〈bit x,R〉〉
   | _ ⇒ 〈q2 c,〈bit x,R〉〉 ]
 | q2 d ⇒ 〈q0,〈d,L〉〉
 | q3 ⇒ 〈q4,〈grid,L〉〉
 | q4 ⇒ (* finale *) ].
*)
(*
MACCHINA B
----------
Sposta il carattere binario su cui si trova la testina oltre il primo # alla sua destra.

Input:

  ls x cs # rs
     ^
     0

Output:
  ls cs # x rs
          ^
          4

STATO 0:
  \forall x.x/R --> 1(x)

STATO 1(x):
  \forall c != #. c/x/L --> 2(c)
  #/x/L --> 3

STATO 2(c):
  \forall d. d/c/R --> 0

STATO 3:
  \forall c. c/#/L --> 4

STATO 4:
  stato finale
*)
(* TODO
match s with
[ q0 ⇒ match c with
  [ bit x ⇒ 〈q1 x,〈c,R〉〉
  | _ ⇒ 〈qsink,〈c,N〉〉]
| q1 x ⇒ match c with
  [ grid ⇒ 〈q3,〈bit x,L〉〉
  | _ ⇒ 〈q2 c,〈bit x,L〉〉 ]
| q2 d ⇒ 〈q0,〈d,R〉〉
| q3 ⇒ 〈q4,〈grid,L〉〉 
| q4 ⇒ (* finale *) ].
*)
(*
MACCHINA C
----------
Sposta il carattere binario su cui si trova la testina appena prima del primo # alla sua destra.

Input:
  ls x cs # rs
     ^
     0

Output:
  ls cs x # rs
        ^
        3

STATO 0:
  \forall x. x/R --> 1(x)

STATO 1(x):
  \forall c != #. c/x/L --> 2(c)
  #/#/L --> 3

STATO 2(c):
  \forall d. d/c/R --> 0

STATO 3:
  stato finale

*)
(* TODO
match s with 
[ q0 ⇒ match c with
  [ bit x ⇒ 〈q1 x,〈c,R〉〉
  | _ ⇒ 〈qsink,〈c,N〉〉 ]
| q1 x ⇒ match c with
  [ grid ⇒ 〈q3,〈grid,L〉〉
  | _ ⇒ 〈q2 c,〈bit x,L〉〉
| q2 d ⇒ 〈q0,〈c,R〉〉
| q3 ⇒ (* finale *) ].
*)