(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department of the University of Bologna, Italy.                     
    ||I||                                                                 
    ||T||  
    ||A||  This file is distributed under the terms of the 
    \   /  GNU General Public License Version 2        
     \ /      
      V_______________________________________________________________ *)

include "pts_dummy_new/reduction.ma".
include "pts_dummy_new/inversion.ma". 

(*
inductive T : Type[0] ≝
  | Sort: nat → T
  | Rel: nat → T 
  | App: T → T → T 
  | Lambda: T → T → T (* type, body *)
  | Prod: T → T → T (* type, body *)
  | D: T →T
. 

inductive red : T →T → Prop ≝
  | rbeta: ∀P,M,N. red (App (Lambda P M) N) (M[0 ≝ N])
  | rappl: ∀M,M1,N. red M M1 → red (App M N) (App M1 N)
  | rappr: ∀M,N,N1. red N N1 → red (App M N) (App M N1)
  | rlaml: ∀M,M1,N. red M M1 → red (Lambda M N) (Lambda M1 N)
  | rlamr: ∀M,N,N1. red N N1 → red(Lambda M N) (Lambda M N1)
  | rprodl: ∀M,M1,N. red M M1 → red (Prod M N) (Prod M1 N)
  | rprodr: ∀M,N,N1. red N N1 → red (Prod M N) (Prod M N1)
  | d: ∀M,M1. red M M1 → red (D M) (D M1). *)
  
lemma lift_D: ∀P,M,N. lift P 0 1 = D M N → 
  ∃M1,N1. M = lift M1 0 1 ∧ N = lift N1 0 1 ∧ P = D M1 N1.   
#P (cases P) normalize
  [#i #M #N #H destruct
  |#i #M #N #H destruct
  |#A #B #M #N #H destruct
  |#A #B #M #N #H destruct
  |#A #B #M #N #H destruct
  |#A #B #M #N #H destruct @(ex_intro … A) @(ex_intro … B) /3/
  ]
qed. 

theorem type_of_type: ∀P,G,A,B. G ⊢_{P} A : B → (∀i. B ≠ Sort i) →
  ∃i. G ⊢_{P} B : Sort i.
#Pts #G #A #B #t (elim t)
  [#i #j #Aij #j @False_ind /2/ 
  |#G1 #A #i #t1 #_ #P @(ex_intro … i) @(weak … t1 t1)
  |#G1 #A #B #C #i #t1 #t2 #H1 #H2 #H3 (cases (H1 ?) )
    [#i #Bi @(ex_intro … i) @(weak … Bi t2)
    |#i @(not_to_not … (H3 i)) /2 width=2/
    ]
  |#G1 #A #B #i #j #k #h #t1 #t2 #_ #_ #H3 @False_ind /2/
  |#G1 #A #B #C #D #t1 #t2 #H1 #H2 #H3 cases (H1 ?);
    [#i #t3 cases (prod_inv … t3 … (refl …))
     #s1 * #s2 * #s3 * * #Ci #H4 #H5 @(ex_intro … s2)
     @(tj_subst_0 … t2 … H5)
    |#i % #H destruct
    ]  
  |#G1 #A #B #C #i #t1 #t2 #H1 #H2 #H3 /2/
  |#G1 #A #B #C #i #ch #t1 #t2 #H1 #H2 #H3 /2/
  |#G1 #A #B #i #t1 #t2 #Hind1 #Hind2 #H /2/
  ]
qed.

lemma prod_sort : ∀Pts,G,M,P,Q. G ⊢_{Pts} M :Prod P Q →
 ∃i. P::G ⊢_{Pts} Q : Sort i.
#Pts #G #M #P #Q #t cases(type_of_type …t ?);
  [#s #t2 cases(prod_inv … t2 …(refl …)) #s1 * #s2 * #s3 * * 
   #_ #_ #H @(ex_intro … s2) //
  | #i % #H destruct
  ]
qed.
    
axiom red_lift: ∀M,N. red (lift M 0 1) N → 
  ∃P. N = lift P 0 1 ∧ red M P. 

theorem tj_d : ∀P,G,M,N,N1. G ⊢_{P} D M N1: N → G ⊢_{P} M : N.
#Pts #G (cut (∀M,N. G ⊢_{Pts} M : N → ∀P,Q. M = D P Q → G ⊢_{Pts} P : N)) [2: /2/] 
#M #N #t (elim t)
  [#i #j #Aij #P #Q #H destruct 
  |#G1 #A #i #t1 #_ #P #Q #H destruct
  |#G1 #A #B #C #i #t1 #t2 #H1 #H2 #P #Q #H3 
   cases (lift_D … H3) #P1 * #Q1 * * #eqP #eqQ #eqA 
   >eqP @(weak … i) /2/
  |#G1 #A #B #i #j #k #h #t1 #t2 #_ #_ #P #Q #H destruct
  |#G1 #A #B #C #D #t1 #t2 #_ #_ #P #Q #H destruct
  |#G1 #A #B #C #D #t1 #t2 #_ #_ #P #Q #H destruct
  |#G1 #A #B #C #i #ch #t1 #t2 #H #_ #P #Q #H
   @(conv… ch …t2) /2/
  |#G1 #A #B #i #t1 #t2 #Hind1 #Hind2 #P #Q #H destruct //
  ]
qed.

definition red0 ≝ λM,N. M = N ∨ red M N.

axiom red_to_conv : ∀P,M,N. red M N → Co P M N.
axiom red0_to_conv : ∀P,M,N. red0 M N → Co P M N.
axiom conv_prod: ∀P,A,B,M,N. Co P A B → Co P M N → 
  Co P (Prod A M) (Prod B N). 
axiom conv_subst_1: ∀Pts,M,P,Q. red P Q → Co Pts (M[0≝Q]) (M[0≝P]).

inductive redG : list T → list T → Prop ≝
 | rnil : redG (nil T) (nil T)
 | rstep : ∀A,B,G1,G2. red0 A B → redG G1 G2 → 
     redG (A::G1) (B::G2).

lemma redG_inv: ∀A,G,G1. redG (A::G) G1 → 
  ∃B. ∃G2. red0 A B ∧ redG G G2 ∧ G1 = B::G2.
#A #G #G1 #rg (inversion rg) 
  [#H destruct
  |#A1 #B1 #G2 #G3 #r1 #r2 #_ #H destruct
   #H1 @(ex_intro … B1) @(ex_intro … G3) % // % //
  ]
qed.

lemma redG_nil: ∀G. redG (nil T) G → G = nil T.
#G #rg (inversion rg) // 
#A #B #G1 #G2 #r1 #r2 #_ #H destruct
qed.

axiom conv_prod_split: ∀P,A,A1,B,B1. 
 Co P(Prod A B) (Prod A1 B1) → Co P A A1 ∧ Co P B B1.

axiom red0_prod : ∀M,N,P. red0 (Prod M N) P → 
  (∃Q. P = Prod Q N ∧ red0 M Q) ∨
  (∃Q. P = Prod M Q ∧ red0 N Q).

theorem subject_reduction: ∀P,G,M,N. G ⊢_{P} M:N → 
 ∀M1. red0 M M1 → ∀G1. redG G G1 → G1 ⊢_{P} M1:N.
#Pts #G #M #N #d (elim d)
  [#i #j #Aij #M1 * 
    [#eqM1 <eqM1 #G1 #H >(redG_nil …H) /2/
    |#H @False_ind /2/
    ]
  |#G1 #A #i #t1 #Hind #M1 * 
    [#eqM1 <eqM1 #G2 #H cases (redG_inv … H)
     #P * #G3 * * #r1 #r2 #eqG2 >eqG2
     @(conv ??? (lift P O 1) ? i);
      [@conv_lift @sym_conv @red0_to_conv //
      |@(start … i) @Hind //
      |@(weak … (Sort i) ? i); [@Hind /2/ | @Hind //]
      ]
    |#H @False_ind /2/
    ]  
  |#G1 #A #B #C #i #t1 #t2 #H1 #H2 #M1 
   #H cases H;
    [#eqM1 <eqM1 #G2 #rg (cases (redG_inv … rg)) 
     #Q * #G3 * * #r2 #rg1 #eqG2 >eqG2 @(weak … i);
      [@H1 /2/ | @H2 //] 
    |#H (elim (red_lift … H)) #P * #eqM1 >eqM1 #redAP
      #G2 #rg (cases (redG_inv … rg)) #Q * #G3 * * #r2 
      #rg1 #eqG2 >eqG2 @(weak … i); 
      [@H1 /2/ | @H2 //]
    ]
  |#G #A #B #i #j #k #Rjk #t1 #t2 #Hind1 #Hind2 #M1 #redP
   (cases (red0_prod … redP))
    [* #M2 * #eqM1 #redA >eqM1 #G1 #rg @(prod … Rjk);
      [@Hind1 // | @Hind2 /2/]
    |* #M2 * #eqM1 #redA >eqM1 #G1 #rg @(prod … Rjk); 
      [@Hind1 /2/ | @Hind2 /3/] 
    ]
  |#G #A #B #C #P #t1 #t2 #Hind1 #Hind2 #M1 #red0a
   (cases red0a)
    [#eqM1 <eqM1 #G1 #rg @(app … B);
      [@Hind1 /2/ | @Hind2 /2/ ]
    |#reda (cases (red_app …reda))
      [*
        [* 
          #M2 * #N1 * #eqA #eqM1 >eqM1 #G1 #rg
           cut (G1 ⊢_{Pts} A: Prod B C); [@Hind1 /2/] #H1
           (cases (abs_inv … H1 … eqA)) #i * #N2 * * 
           #cProd #t3 #t4 
           (cut (Co Pts B M2 ∧ Co Pts C N2) ) [/2/] * #convB #convC
           (cases (prod_inv … t3 … (refl …) )) #i * #j * #k * *
           #cik #t5 #t6 (cut (G1 ⊢_{Pts} P:B)) 
            [@Hind2 /2/
            |#Hcut cut (G1 ⊢_{Pts} N1[0:=P] : N2 [0:=P]);
              [@(tj_subst_0 … M2) // @(conv … convB Hcut t5)
              |#Hcut1 cases (prod_sort … H1) #s #Csort
               @(conv … s  … Hcut1); 
                [@conv_subst /2/ | @(tj_subst_0 … Csort) //]
              ]
            ]
        |* #M2 * #eqM1 >eqM1 #H #G1 #rg @(app … B);
          [@Hind1 /2/ | @Hind2 /2/] 
        ]      
      |* #M2 * #eqM1 >eqM1 #H #G1 #rg 
       cut (G1 ⊢_{Pts} A:Prod B C); [@Hind1 /2/] #t3
       cases (prod_sort …t3) #i #Csort @(conv ??? C[O≝ M2] … i);
        [@conv_subst_1 //
        |@(app … B)  // @Hind2 /2/
        |@(tj_subst_0 … Csort) @Hind2 /2/
        ]
      ]
    ]
  |#G #A #B #C #i #t1 #t2 #Hind1 #Hind2 #M2 #red0l #G1 #rg
   cut (A::G1⊢_{Pts} C:B); [@Hind1 /3/] #t3
   cut (G1 ⊢_{Pts} Prod A B : Sort i); [@Hind2 /2/] #t4
   cases red0l;
    [#eqM2 <eqM2 @(abs … t3 t4)
    |#redl (cases (red_lambda … redl))  
      [* #M3 * #eqM2 #redA >eqM2 
         @(conv ??? (Prod M3 B) … t4);
          [@conv_prod /2/
          |@(abs … i); [@Hind1 /3/ |@Hind2 /3/]
          ]
        |* #M3 * #eqM3 #redC >eqM3
         @(abs … t4) @Hind1 /3/
      ]
    ]
  |#G #A #B #C #i #convBC #t1 #t2 #Hind1 #Hind2 #M1 #redA
   #G1 #rg @(conv … i … convBC); [@Hind1 // |@Hind2 /2/]
  |#G #A #B #i #t1 #t2 #Hind1 #Hind2 #M1 #red0d #G1 #rg
   cases red0d; 
    [#eqM1 <eqM1 @(dummy … i); [@Hind1 /2/ |@Hind2 /2/] 
    |#redd (cases (red_d … redd))
      [* #A1 * #eqM1 #redA >eqM1 
       @(dummy … i);[@Hind1 /2/ |@Hind2 /2/]
      |* #B1 * #eqM1 #redB >eqM1 
       cut (G1 ⊢_{Pts} B: Sort i); [@Hind2 /2/] #sB
       cut (G1 ⊢_{Pts} B1: Sort i); [@Hind2 /2/] #sB1
       @(conv … B1 … i) /2/ @(dummy … i) // @(conv … B … i) /2/ 
       @Hind1 /2/
      ]
    ]
  ]
qed.

