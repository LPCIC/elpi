(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "lambda/paths/path.ma".

(* STANDARD PRECEDENCE ******************************************************)

(* Note: standard precedence relation on paths: p ≺ q
         to serve as base for the order relations: p < q and p ≤ q *)
inductive sprec: relation path ≝
| sprec_nil : ∀o,q.   sprec (◊) (o::q)
| sprec_rc  : ∀p,q.   sprec (dx::p) (rc::q)
| sprec_sn  : ∀p,q.   sprec (rc::p) (sn::q)
| sprec_comp: ∀o,p,q. sprec p q → sprec (o::p) (o::q)
| sprec_skip:         sprec (dx::◊) ◊
.

interpretation "standard 'precedes' on paths"
   'prec p q = (sprec p q).

lemma sprec_inv_sn: ∀p,q. p ≺ q → ∀p0. sn::p0 = p →
                    ∃∃q0. p0 ≺ q0 & sn::q0 = q.
#p #q * -p -q
[ #o #q #p0 #H destruct
| #p #q #p0 #H destruct
| #p #q #p0 #H destruct
| #o #p #q #Hpq #p0 #H destruct /2 width=3/
| #p0 #H destruct
]
qed-.

lemma sprec_inv_dx: ∀p,q. p ≺ q → ∀q0. dx::q0 = q →
                    ◊ = p ∨ ∃∃p0. p0 ≺ q0 & dx::p0 = p.
#p #q * -p -q
[ #o #q #q0 #H destruct /2 width=1/
| #p #q #q0 #H destruct
| #p #q #q0 #H destruct
| #o #p #q #Hpq #q0 #H destruct /3 width=3/
| #q0 #H destruct
]
qed-.

lemma sprec_inv_rc: ∀p,q. p ≺ q → ∀p0. rc::p0 = p →
                    (∃∃q0. p0 ≺ q0 & rc::q0 = q) ∨
                    ∃q0. sn::q0 = q.
#p #q * -p -q
[ #o #q #p0 #H destruct
| #p #q #p0 #H destruct
| #p #q #p0 #H destruct /3 width=2/
| #o #p #q #Hpq #p0 #H destruct /3 width=3/
| #p0 #H destruct
]
qed-.

lemma sprec_inv_comp: ∀p1,p2. p1 ≺ p2 →
                      ∀o,q1,q2. o::q1 = p1 → o::q2 = p2 → q1 ≺ q2.
#p1 #p2 * -p1 -p2
[ #o #q #o0 #q1 #q2 #H destruct
| #p #q #o0 #q1 #q2 #H1 #H2 destruct
| #p #q #o0 #q1 #q2 #H1 #H2 destruct
| #o #p #q #Hpq #o0 #q1 #q2 #H1 #H2 destruct //
| #o0 #q1 #q2 #_ #H destruct
]
qed-.

lemma sprec_fwd_in_whd: ∀p,q. p ≺ q → in_whd q → in_whd p.
#p #q #H elim H -p -q // /2 width=1/
[ #p #q * #H destruct
| #p #q * #H destruct
| #o #p #q #_ #IHpq * #H destruct /3 width=1/
]
qed-.

lemma sprec_fwd_in_inner: ∀p,q. p ≺ q → in_inner p → in_inner q.
/3 width=3 by sprec_fwd_in_whd/
qed-.
