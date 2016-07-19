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

include "arithmetics/nat.ma".
include "basics/lists/list.ma".

interpretation "iff" 'iff a b = (iff a b).  

record Alpha : Type[1] ≝ { carr :> Type[0];
   eqb: carr → carr → bool;
   eqb_true: ∀x,y. (eqb x y = true) ↔ (x = y)
}.
 
notation "a == b" non associative with precedence 45 for @{ 'eqb $a $b }.
interpretation "eqb" 'eqb a b = (eqb ? a b).

definition word ≝ λS:Alpha.list S.

let rec eqbw S (x,y:word S) on x ≝ 
  match x with
  [ nil ⇒ match y with [nil ⇒ true | _ ⇒ false]
  | cons a xtl ⇒ match y with 
    [nil ⇒ false | cons b ytl ⇒ a == b ∧ eqbw S xtl ytl ]
  ]
.

inductive re (S: Alpha) : Type[0] ≝
   z: re S
 | e: re S
 | s: S → re S
 | c: re S → re S → re S
 | o: re S → re S → re S
 | k: re S → re S.
 
notation < "a \sup ⋇" non associative with precedence 90 for @{ 'pk $a}.
notation > "a ^ *" non associative with precedence 90 for @{ 'pk $a}.
interpretation "star" 'pk a = (k ? a).
interpretation "or" 'plus a b = (o ? a b).
           
notation "a · b" non associative with precedence 65 for @{ 'pc $a $b}.
interpretation "cat" 'pc a b = (c ? a b).

(* to get rid of \middot 
ncoercion c  : ∀S:Alpha.∀p:re S.  re S →  re S   ≝ c  on _p : re ?  to ∀_:?.?.
*)

notation < "a" non associative with precedence 90 for @{ 'ps $a}.
notation > "` term 90 a" non associative with precedence 90 for @{ 'ps $a}.
interpretation "atom" 'ps a = (s ? a).

notation "ϵ" non associative with precedence 90 for @{ 'epsilon }.
interpretation "epsilon" 'epsilon = (e ?).

notation "∅" non associative with precedence 90 for @{ 'empty }.
interpretation "empty" 'empty = (z ?).

let rec flatten (S : Alpha) (l : list (word S)) on l : word S ≝ 
match l with [ nil ⇒ [ ] | cons w tl ⇒ w @ flatten ? tl ].

let rec conjunct (S : Alpha) (l : list (word S)) (r : word S → bool) on l: bool ≝
match l with [ nil ⇒ true | cons w tl ⇒ r w ∧ conjunct ? tl r ]. 

definition empty_lang ≝ λS.λw:word S.false.
notation "{}" non associative with precedence 90 for @{'empty_lang}.
interpretation "empty lang" 'empty_lang = (empty_lang ?).

definition sing_lang ≝ λS.λx,w:word S.eqbw S x w.
(* notation "{x}" non associative with precedence 90 for @{'sing_lang $x}.*)
interpretation "sing lang" 'singl x = (sing_lang ? x).

definition union : ∀S,l1,l2,w.Prop ≝ λS.λl1,l2.λw:word S.l1 w ∨ l2 w.
interpretation "union lang" 'union a b = (union ? a b).

definition cat : ∀S,l1,l2,w.Prop ≝ 
  λS.λl1,l2.λw:word S.∃w1,w2.w1 @ w2 = w ∧ l1 w1 ∧ l2 w2.
interpretation "cat lang" 'pc a b = (cat ? a b).

(* BEGIN HERE 

definition star ≝ λS.λl.λw:word S.∃lw.flatten ? lw = w ∧ conjunct ? lw l. 
interpretation "star lang" 'pk l = (star ? l).

let rec in_l (S : Alpha) (r : re S) on r : word S → Prop ≝ 
match r with
[ z ⇒ {}
| e ⇒ { [ ] }
| s x ⇒ { [x] }
| c r1 r2 ⇒ (in_l ? r1) · (in_l ? r2)
| o r1 r2 ⇒ (in_l ? r1) ∪ (in_l ? r2)
| k r1 ⇒ (in_l ? r1) ^*].

notation "\sem{E}" non associative with precedence 75 for @{'in_l $E}.
interpretation "in_l" 'in_l E = (in_l ? E).
interpretation "in_l mem" 'mem w l = (in_l ? l w).

notation "a || b" left associative with precedence 30 for @{'orb $a $b}.
interpretation "orb" 'orb a b = (orb a b).

definition if_then_else ≝ λT:Type[0].λe,t,f.match e return λ_.T with [ true ⇒ t | false ⇒ f].
notation > "'if' term 19 e 'then' term 19 t 'else' term 19 f" non associative with precedence 19 for @{ 'if_then_else $e $t $f }.
notation < "'if' \nbsp term 19 e \nbsp 'then' \nbsp term 19 t \nbsp 'else' \nbsp term 90 f \nbsp" non associative with precedence 19 for @{ 'if_then_else $e $t $f }.
interpretation "if_then_else" 'if_then_else e t f = (if_then_else ? e t f).

inductive pitem (S: Alpha) : Type[0] ≝
   pz: pitem S
 | pe: pitem S
 | ps: S → pitem S
 | pp: S → pitem S
 | pc: pitem S → pitem S → pitem S
 | po: pitem S → pitem S → pitem S
 | pk: pitem S → pitem S.
 
definition pre ≝ λS.pitem S × bool.

interpretation "pstar" 'pk a = (pk ? a).
interpretation "por" 'plus a b = (po ? a b).
interpretation "pcat" 'pc a b = (pc ? a b).
notation < ".a" non associative with precedence 90 for @{ 'pp $a}.
notation > "`. term 90 a" non associative with precedence 90 for @{ 'pp $a}.
interpretation "ppatom" 'pp a = (pp ? a).
(* to get rid of \middot 
ncoercion pc : ∀S.∀p:pitem S. pitem S → pitem S  ≝ pc on _p : pitem ? to ∀_:?.?.
*)
interpretation "patom" 'ps a = (ps ? a).
interpretation "pepsilon" 'epsilon = (pe ?).
interpretation "pempty" 'empty = (pz ?).

notation > "| e |" non associative with precedence 66 for @{forget ? $e}.
let rec forget (S: Alpha) (l : pitem S) on l: re S ≝
 match l with
  [ pz ⇒ ∅
  | pe ⇒ ϵ
  | ps x ⇒ `x
  | pp x ⇒ `x
  | pc E1 E2 ⇒ (forget ? E1) · (forget ? E2)
  | po E1 E2 ⇒ (forget ? E1) + (forget ? E2)
  | pk E ⇒ (forget ? E)^* ].
  
notation < "|term 19 e|" non associative with precedence 70 for @{'forget $e}.
interpretation "forget" 'forget a = (forget ? a).


let rec in_pl (S : Alpha) (r : pitem S) on r : word S → Prop ≝ 
match r with
[ pz ⇒ {}
| pe ⇒ {}
| ps _ ⇒ {}
| pp x ⇒ { [x] }
| pc r1 r2 ⇒ (in_pl ? r1) · \sem{forget ? r2} ∪ (in_pl ? r2)
| po r1 r2 ⇒ (in_pl ? r1) ∪ (in_pl ? r2)
| pk r1 ⇒ (in_pl ? r1) · \sem{forget ? r1}^*  ].

interpretation "in_pl" 'in_l E = (in_pl ? E).
interpretation "in_pl mem" 'mem w l = (in_pl ? l w).

definition epsilon ≝ λS,b.if b then { ([ ] : word S) } else {}.

interpretation "epsilon" 'epsilon = (epsilon ?).
notation < "ϵ b" non associative with precedence 90 for @{'app_epsilon $b}.
interpretation "epsilon lang" 'app_epsilon b = (epsilon ? b).

definition in_prl ≝ λS : Alpha.λp:pre S. \sem{\fst p} ∪ ϵ (\snd p).
  
interpretation "in_prl mem" 'mem w l = (in_prl ? l w).
interpretation "in_prl" 'in_l E = (in_prl ? E).

lemma append_eq_nil : ∀S.∀w1,w2:word S. w1 @ w2 = [ ] → w1 = [ ].
#S #w1 #w2 cases w1 // #a #tl normalize #H destruct qed.

lemma not_epsilon_lp : ∀S:Alpha.∀e:pitem S. ¬ ([ ] ∈ e).
#S #e elim e normalize /2/  
  [#r1 #r2 * #n1 #n2 % * /2/ * #w1 * #w2 * * #H 
   >(append_eq_nil …H…) /2/
  |#r1 #r2 #n1 #n2 % * /2/
  |#r #n % * #w1 * #w2 * * #H >(append_eq_nil …H…) /2/
  ]
qed.

(* lemma 12 *)
lemma epsilon_to_true : ∀S.∀e:pre S. [ ] ∈ e → \snd e = true.
#S #r * [#H apply False_ind /2/ | cases (\snd r) normalize // * ;
qed.

lemma true_to_epsilon : ∀S.∀e:pre S. \snd e = true → [ ] ∈ e.
#S #e #H %2 >H // 
qed.

definition lo ≝ λS:Alpha.λa,b:pre S.〈\fst a + \fst b,\snd a || \snd b〉.
notation "a ⊕ b" left associative with precedence 65 for @{'oplus $a $b}.
interpretation "oplus" 'oplus a b = (lo ? a b).

lemma lo_def: ∀S.∀i1,i2:pitem S.∀b1,b2. 〈i1,b1〉⊕〈i2,b2〉=〈i1+i2,b1||b2〉.
// qed.

definition item_concat ≝ λS:Alpha.λi:pitem S.λe:pre S.
  match e with [ pair i1 b ⇒ 〈i · i1, b〉].

definition lc ≝ λS:Alpha.λbcast:∀S:Alpha.pre S → pre S.λe1.λe2:pre S.
  match e1 with 
  [ pair i1 b1 ⇒ match b1 with 
    [ true ⇒ item_concat ? i1 (bcast ? e2) 
    | false ⇒ item_concat ? i1 e2
    ]
  ].
        
definition lift ≝ λf:∀S.pitem S →pre S.λS.λe:pre S. 
  match e with 
  [ pair i b ⇒ 〈\fst (f S i), \snd (f S i) || b〉].

notation < "a ⊙ b" left associative with precedence 65 for @{'lc $op $a $b}.
interpretation "lc" 'lc op a b = (lc ? op a b).
notation > "a ⊙ b" left associative with precedence 65 for @{'lc (lift eclose) $a $b}.

definition lk ≝ λS:Alpha.λbcast:∀S:Alpha.∀E:pitem S.pre S.λe:pre S.
  match e with 
  [ pair i1 b1 ⇒
    match b1 with 
    [true ⇒ 〈(\fst (bcast ? i1))^*, true〉
    |false ⇒ 〈i1^*,true〉
    ]
  ].

notation < "a \sup ⊛" non associative with precedence 90 for @{'lk $op $a}.
interpretation "lk" 'lk op a = (lk ? op a).
notation > "a^⊛" non associative with precedence 90 for @{'lk eclose $a}.


notation > "•" non associative with precedence 65 for @{eclose ?}.
let rec eclose (S: Alpha) (i: pitem S) on i : pre S ≝
 match i with
  [ pz ⇒ 〈 ∅, false 〉
  | pe ⇒ 〈 ϵ,  true 〉
  | ps x ⇒ 〈 `.x, false〉
  | pp x ⇒ 〈 `.x, false 〉
  | po E1 E2 ⇒ •E1 ⊕ •E2
  | pc E1 E2 ⇒ •E1 ⊙ 〈E2,false〉
  | pk E ⇒ 〈(\fst(•E))^*,true〉].
  
notation < "• x" non associative with precedence 65 for @{'eclose $x}.
interpretation "eclose" 'eclose x = (eclose ? x).
notation > "• x" non associative with precedence 65 for @{'eclose $x}.

definition reclose ≝ lift eclose.
interpretation "reclose" 'eclose x = (reclose ? x).

definition eq_f1 ≝ λS.λa,b:word S → Prop.∀w.a w ↔ b w.
notation "A ≐ B" non associative with precedence 45 for @{'eq_f1 $A $B}.
interpretation "eq f1" 'eq_f1 a b = (eq_f1 ? a b).

(*
lemma epsilon_or : ∀S:Alpha.∀b1,b2. ϵ(b1 || b2) ≐ ϵ b1 ∪ ϵ b2. 
##[##2: napply S]
#S b1 b2; ncases b1; ncases b2; napply extP; #w; nnormalize; @; /2/; *; //; *;
nqed.

lemma cupA : ∀S.∀a,b,c:word S → Prop.a ∪ b ∪ c = a ∪ (b ∪ c).
#S a b c; napply extP; #w; nnormalize; @; *; /3/; *; /3/; nqed.

nlemma cupC : ∀S. ∀a,b:word S → Prop.a ∪ b = b ∪ a.
#S a b; napply extP; #w; @; *; nnormalize; /2/; nqed.*)

(* theorem 16: 2 *)
lemma oplus_cup : ∀S:Alpha.∀e1,e2:pre S.\sem{e1 ⊕ e2} ≐ \sem{e1} ∪ \sem{e2}.
#S * #i1 #b1  * #i2 #b2 >lo_def normalize in ⊢ (?%?);

#w cases b1 cases b2 normalize % #w r1; ncases r1; #e1 b1 r2; ncases r2; #e2 b2;
nwhd in ⊢ (??(??%)?);
nchange in ⊢(??%?) with (𝐋\p (e1 + e2) ∪ ϵ (b1 || b2));
nchange in ⊢(??(??%?)?) with (𝐋\p (e1) ∪ 𝐋\p (e2));
nrewrite > (epsilon_or S …); nrewrite > (cupA S (𝐋\p e1) …);
nrewrite > (cupC ? (ϵ b1) …); nrewrite < (cupA S (𝐋\p e2) …);
nrewrite > (cupC ? ? (ϵ b1) …); nrewrite < (cupA …); //;
nqed.

nlemma odotEt : 
  ∀S.∀e1,e2:pitem S.∀b2. 〈e1,true〉 ⊙ 〈e2,b2〉 = 〈e1 · \fst (•e2),b2 || \snd (•e2)〉.
#S e1 e2 b2; nnormalize; ncases (•e2); //; nqed.

nlemma LcatE : ∀S.∀e1,e2:pitem S.𝐋\p (e1 · e2) =  𝐋\p e1 · 𝐋 |e2| ∪ 𝐋\p e2. //; nqed.

nlemma cup_dotD : ∀S.∀p,q,r:word S → Prop.(p ∪ q) · r = (p · r) ∪ (q · r). 
#S p q r; napply extP; #w; nnormalize; @; 
##[ *; #x; *; #y; *; *; #defw; *; /7/ by or_introl, or_intror, ex_intro, conj;
##| *; *; #x; *; #y; *; *; /7/ by or_introl, or_intror, ex_intro, conj; ##]
nqed.

nlemma cup0 :∀S.∀p:word S → Prop.p ∪ {} = p.
#S p; napply extP; #w; nnormalize; @; /2/; *; //; *; nqed.

nlemma erase_dot : ∀S.∀e1,e2:pitem S.𝐋 |e1 · e2| =  𝐋 |e1| · 𝐋 |e2|.
#S e1 e2; napply extP; nnormalize; #w; @; *; #w1; *; #w2; *; *; /7/ by ex_intro, conj;
nqed.

nlemma erase_plus : ∀S.∀e1,e2:pitem S.𝐋 |e1 + e2| =  𝐋 |e1| ∪ 𝐋 |e2|.
#S e1 e2; napply extP; nnormalize; #w; @; *; /4/ by or_introl, or_intror; nqed.

nlemma erase_star : ∀S.∀e1:pitem S.𝐋 |e1|^* = 𝐋 |e1^*|. //; nqed.

ndefinition substract := λS.λp,q:word S → Prop.λw.p w ∧ ¬ q w.
interpretation "substract" 'minus a b = (substract ? a b).

nlemma cup_sub: ∀S.∀a,b:word S → Prop. ¬ (a []) → a ∪ (b - {[]}) = (a ∪ b) - {[]}.
#S a b c; napply extP; #w; nnormalize; @; *; /4/; *; /4/; nqed.

nlemma sub0 : ∀S.∀a:word S → Prop. a - {} = a.
#S a; napply extP; #w; nnormalize; @; /3/; *; //; nqed.

nlemma subK : ∀S.∀a:word S → Prop. a - a = {}.
#S a; napply extP; #w; nnormalize; @; *; /2/; nqed.

nlemma subW : ∀S.∀a,b:word S → Prop.∀w.(a - b) w → a w.
#S a b w; nnormalize; *; //; nqed.

nlemma erase_bull : ∀S.∀a:pitem S. |\fst (•a)| = |a|.
#S a; nelim a; // by {};
##[ #e1 e2 IH1 IH2; nchange in ⊢ (???%) with (|e1| · |e2|);
    nrewrite < IH1; nrewrite < IH2;  
    nchange in ⊢ (??(??%)?) with (\fst (•e1 ⊙ 〈e2,false〉));
    ncases (•e1); #e3 b; ncases b; nnormalize;
    ##[ ncases (•e2); //; ##| nrewrite > IH2; //]
##| #e1 e2 IH1 IH2; nchange in ⊢ (???%) with (|e1| + |e2|);
    nrewrite < IH2; nrewrite < IH1;
    nchange in ⊢ (??(??%)?) with (\fst (•e1 ⊕ •e2));
    ncases (•e1); ncases (•e2); //;
##| #e IH; nchange in ⊢ (???%) with (|e|^* ); nrewrite < IH;
    nchange in ⊢ (??(??%)?) with (\fst (•e))^*; //; ##]
nqed.

nlemma eta_lp : ∀S.∀p:pre S.𝐋\p p = 𝐋\p 〈\fst p, \snd p〉.
#S p; ncases p; //; nqed.

nlemma epsilon_dot: ∀S.∀p:word S → Prop. {[]} · p = p. 
#S e; napply extP; #w; nnormalize; @; ##[##2: #Hw; @[]; @w; /3/; ##]
*; #w1; *; #w2; *; *; #defw defw1 Hw2; nrewrite < defw; nrewrite < defw1;
napply Hw2; nqed.

(* theorem 16: 1 → 3 *)
nlemma odot_dot_aux : ∀S.∀e1,e2: pre S.
      𝐋\p (•(\fst e2)) =  𝐋\p (\fst e2) ∪ 𝐋 |\fst e2| → 
         𝐋\p (e1 ⊙ e2) =  𝐋\p e1 · 𝐋 |\fst e2| ∪ 𝐋\p e2.
#S e1 e2 th1; ncases e1; #e1' b1'; ncases b1';
##[ nwhd in ⊢ (??(??%)?); nletin e2' ≝ (\fst e2); nletin b2' ≝ (\snd e2); 
    nletin e2'' ≝ (\fst (•(\fst e2))); nletin b2'' ≝ (\snd (•(\fst e2)));
    nchange in ⊢ (??%?) with (?∪?); 
    nchange in ⊢ (??(??%?)?) with (?∪?);
    nchange in match (𝐋\p 〈?,?〉) with (?∪?);
    nrewrite > (epsilon_or …); nrewrite > (cupC ? (ϵ ?)…);
    nrewrite > (cupA …);nrewrite < (cupA ?? (ϵ?)…);
    nrewrite > (?: 𝐋\p e2'' ∪ ϵ b2'' = 𝐋\p e2' ∪ 𝐋 |e2'|); ##[##2:
      nchange with (𝐋\p 〈e2'',b2''〉 =  𝐋\p e2' ∪ 𝐋 |e2'|); 
      ngeneralize in match th1;
      nrewrite > (eta_lp…); #th1; nrewrite > th1; //;##]
    nrewrite > (eta_lp ? e2); 
    nchange in match (𝐋\p 〈\fst e2,?〉) with (𝐋\p e2'∪ ϵ b2');
    nrewrite > (cup_dotD …); nrewrite > (epsilon_dot…);       
    nrewrite > (cupC ? (𝐋\p e2')…); nrewrite > (cupA…);nrewrite > (cupA…);
    nrewrite < (erase_bull S e2') in ⊢ (???(??%?)); //;
##| ncases e2; #e2' b2'; nchange in match (〈e1',false〉⊙?) with 〈?,?〉;
    nchange in match (𝐋\p ?) with (?∪?);
    nchange in match (𝐋\p (e1'·?)) with (?∪?);
    nchange in match (𝐋\p 〈e1',?〉) with (?∪?);
    nrewrite > (cup0…); 
    nrewrite > (cupA…); //;##]
nqed.

nlemma sub_dot_star : 
  ∀S.∀X:word S → Prop.∀b. (X - ϵ b) · X^* ∪ {[]} = X^*.
#S X b; napply extP; #w; @;
##[ *; ##[##2: nnormalize; #defw; nrewrite < defw; @[]; @; //]
    *; #w1; *; #w2; *; *; #defw sube; *; #lw; *; #flx cj;
    @ (w1 :: lw); nrewrite < defw; nrewrite < flx; @; //;
    @; //; napply (subW … sube);
##| *; #wl; *; #defw Pwl; nrewrite < defw; nelim wl in Pwl; ##[ #_; @2; //]
    #w' wl' IH; *; #Pw' IHp; nlapply (IH IHp); *;
    ##[ *; #w1; *; #w2; *; *; #defwl' H1 H2;
        @; ncases b in H1; #H1; 
        ##[##2: nrewrite > (sub0…); @w'; @(w1@w2);
                nrewrite > (associative_append ? w' w1 w2);
                nrewrite > defwl'; @; ##[@;//] @(wl'); @; //;
           ##| ncases w' in Pw';
               ##[ #ne; @w1; @w2; nrewrite > defwl'; @; //; @; //;
               ##| #x xs Px; @(x::xs); @(w1@w2); 
                   nrewrite > (defwl'); @; ##[@; //; @; //; @; nnormalize; #; ndestruct]
                   @wl'; @; //; ##] ##]
        ##| #wlnil; nchange in match (flatten ? (w'::wl')) with (w' @ flatten ? wl');
            nrewrite < (wlnil); nrewrite > (append_nil…); ncases b;
            ##[ ncases w' in Pw'; /2/; #x xs Pxs; @; @(x::xs); @([]);
                nrewrite > (append_nil…); @; ##[ @; //;@; //; nnormalize; @; #; ndestruct]
                @[]; @; //;
            ##| @; @w'; @[]; nrewrite > (append_nil…); @; ##[##2: @[]; @; //] 
                @; //; @; //; @; *;##]##]##] 
nqed.

(* theorem 16: 1 *)
alias symbol "pc" (instance 13) = "cat lang".
alias symbol "in_pl" (instance 23) = "in_pl".
alias symbol "in_pl" (instance 5) = "in_pl".
alias symbol "eclose" (instance 21) = "eclose".
ntheorem bull_cup : ∀S:Alpha. ∀e:pitem S.  𝐋\p (•e) =  𝐋\p e ∪ 𝐋 |e|.
#S e; nelim e; //;
  ##[ #a; napply extP; #w; nnormalize; @; *; /3/ by or_introl, or_intror;
  ##| #a; napply extP; #w; nnormalize; @; *; /3/ by or_introl; *;
  ##| #e1 e2 IH1 IH2;  
      nchange in ⊢ (??(??(%))?) with (•e1 ⊙ 〈e2,false〉);
      nrewrite > (odot_dot_aux S (•e1) 〈e2,false〉 IH2);
      nrewrite > (IH1 …); nrewrite > (cup_dotD …);
      nrewrite > (cupA …); nrewrite > (cupC ?? (𝐋\p ?) …);
      nchange in match (𝐋\p 〈?,?〉) with (𝐋\p e2 ∪ {}); nrewrite > (cup0 …);
      nrewrite < (erase_dot …); nrewrite < (cupA …); //;
  ##| #e1 e2 IH1 IH2;
      nchange in match (•(?+?)) with (•e1 ⊕ •e2); nrewrite > (oplus_cup …);
      nrewrite > (IH1 …); nrewrite > (IH2 …); nrewrite > (cupA …);
      nrewrite > (cupC ? (𝐋\p e2)…);nrewrite < (cupA ??? (𝐋\p e2)…);
      nrewrite > (cupC ?? (𝐋\p e2)…); nrewrite < (cupA …); 
      nrewrite < (erase_plus …); //.
  ##| #e; nletin e' ≝ (\fst (•e)); nletin b' ≝ (\snd (•e)); #IH;
      nchange in match (𝐋\p ?) with  (𝐋\p 〈e'^*,true〉);
      nchange in match (𝐋\p ?) with (𝐋\p (e'^* ) ∪ {[ ]});
      nchange in ⊢ (??(??%?)?) with (𝐋\p e' · 𝐋 |e'|^* );
      nrewrite > (erase_bull…e);
      nrewrite > (erase_star …);
      nrewrite > (?: 𝐋\p e' =  𝐋\p e ∪ (𝐋 |e| - ϵ b')); ##[##2:
        nchange in IH : (??%?) with (𝐋\p e' ∪ ϵ b'); ncases b' in IH; 
        ##[ #IH; nrewrite > (cup_sub…); //; nrewrite < IH; 
            nrewrite < (cup_sub…); //; nrewrite > (subK…); nrewrite > (cup0…);//;
        ##| nrewrite > (sub0 …); #IH; nrewrite < IH; nrewrite > (cup0 …);//; ##]##]
      nrewrite > (cup_dotD…); nrewrite > (cupA…); 
      nrewrite > (?: ((?·?)∪{[]} = 𝐋 |e^*|)); //;
      nchange in match (𝐋 |e^*|) with ((𝐋 |e|)^* ); napply sub_dot_star;##]
 nqed.

(* theorem 16: 3 *)      
nlemma odot_dot: 
  ∀S.∀e1,e2: pre S.  𝐋\p (e1 ⊙ e2) =  𝐋\p e1 · 𝐋 |\fst e2| ∪ 𝐋\p e2.
#S e1 e2; napply odot_dot_aux; napply (bull_cup S (\fst e2)); nqed.

nlemma dot_star_epsilon : ∀S.∀e:re S.𝐋 e · 𝐋 e^* ∪ {[]} =  𝐋 e^*.
#S e; napply extP; #w; nnormalize; @;
##[ *; ##[##2: #H; nrewrite < H; @[]; /3/] *; #w1; *; #w2; 
    *; *; #defw Hw1; *; #wl; *; #defw2 Hwl; @(w1 :: wl);
    nrewrite < defw; nrewrite < defw2; @; //; @;//;
##| *; #wl; *; #defw Hwl; ncases wl in defw Hwl; ##[#defw; #; @2; nrewrite < defw; //]
    #x xs defw; *; #Hx Hxs; @; @x; @(flatten ? xs); nrewrite < defw;
    @; /2/; @xs; /2/;##]
 nqed.

nlemma nil_star : ∀S.∀e:re S. [ ] ∈ e^*.
#S e; @[]; /2/; nqed.

nlemma cupID : ∀S.∀l:word S → Prop.l ∪ l = l.
#S l; napply extP; #w; @; ##[*]//; #; @; //; nqed.

nlemma cup_star_nil : ∀S.∀l:word S → Prop. l^* ∪ {[]} = l^*.
#S a; napply extP; #w; @; ##[*; //; #H; nrewrite < H; @[]; @; //] #;@; //;nqed.

nlemma rcanc_sing : ∀S.∀A,C:word S → Prop.∀b:word S .
  ¬ (A b) → A ∪ { (b) } = C → A = C - { (b) }.
#S A C b nbA defC; nrewrite < defC; napply extP; #w; @;
##[ #Aw; /3/| *; *; //; #H nH; ncases nH; #abs; nlapply (abs H); *]
nqed.

(* theorem 16: 4 *)      
nlemma star_dot: ∀S.∀e:pre S. 𝐋\p (e^⊛) = 𝐋\p e · (𝐋 |\fst e|)^*.
#S p; ncases p; #e b; ncases b;
##[ nchange in match (〈e,true〉^⊛) with 〈?,?〉;
    nletin e' ≝ (\fst (•e)); nletin b' ≝ (\snd (•e));
    nchange in ⊢ (??%?) with (?∪?);
    nchange in ⊢ (??(??%?)?) with (𝐋\p e' · 𝐋 |e'|^* );
    nrewrite > (?: 𝐋\p e' = 𝐋\p e ∪ (𝐋 |e| - ϵ b' )); ##[##2:
      nlapply (bull_cup ? e); #bc;
      nchange in match (𝐋\p (•e)) in bc with (?∪?);
      nchange in match b' in bc with b';
      ncases b' in bc; ##[##2: nrewrite > (cup0…); nrewrite > (sub0…); //]
      nrewrite > (cup_sub…); ##[napply rcanc_sing] //;##]
    nrewrite > (cup_dotD…); nrewrite > (cupA…);nrewrite > (erase_bull…);
    nrewrite > (sub_dot_star…);
    nchange in match (𝐋\p 〈?,?〉) with (?∪?);
    nrewrite > (cup_dotD…); nrewrite > (epsilon_dot…); //;    
##| nwhd in match (〈e,false〉^⊛); nchange in match (𝐋\p 〈?,?〉) with (?∪?);
    nrewrite > (cup0…);
    nchange in ⊢ (??%?) with (𝐋\p e · 𝐋 |e|^* );
    nrewrite < (cup0 ? (𝐋\p e)); //;##]
nqed.

nlet rec pre_of_re (S : Alpha) (e : re S) on e : pitem S ≝ 
  match e with 
  [ z ⇒ pz ?
  | e ⇒ pe ?
  | s x ⇒ ps ? x
  | c e1 e2 ⇒ pc ? (pre_of_re ? e1) (pre_of_re ? e2)
  | o e1 e2 ⇒ po ? (pre_of_re ? e1) (pre_of_re ? e2)
  | k e1 ⇒ pk ? (pre_of_re ? e1)].

nlemma notFalse : ¬False. @; //; nqed.

nlemma dot0 : ∀S.∀A:word S → Prop. {} · A = {}.
#S A; nnormalize; napply extP; #w; @; ##[##2: *]
*; #w1; *; #w2; *; *; //; nqed.

nlemma Lp_pre_of_re : ∀S.∀e:re S. 𝐋\p (pre_of_re ? e) = {}.
#S e; nelim e; ##[##1,2,3: //]
##[ #e1 e2 H1 H2; nchange in match (𝐋\p (pre_of_re S (e1 e2))) with (?∪?);
    nrewrite > H1; nrewrite > H2; nrewrite > (dot0…); nrewrite > (cupID…);//
##| #e1 e2 H1 H2; nchange in match (𝐋\p (pre_of_re S (e1+e2))) with (?∪?);
    nrewrite > H1; nrewrite > H2; nrewrite > (cupID…); //
##| #e1 H1; nchange in match (𝐋\p (pre_of_re S (e1^* ))) with (𝐋\p (pre_of_re ??) · ?);
    nrewrite > H1; napply dot0; ##]
nqed.

nlemma erase_pre_of_reK : ∀S.∀e. 𝐋 |pre_of_re S e| = 𝐋 e.
#S A; nelim A; //; 
##[ #e1 e2 H1 H2; nchange in match (𝐋 (e1 · e2)) with (𝐋 e1·?);
    nrewrite < H1; nrewrite < H2; //
##| #e1 e2 H1 H2; nchange in match (𝐋 (e1 + e2)) with (𝐋 e1 ∪ ?);
    nrewrite < H1; nrewrite < H2; //
##| #e1 H1; nchange in match (𝐋  (e1^* )) with ((𝐋 e1)^* );
    nrewrite < H1; //]
nqed.     

(* corollary 17 *)
nlemma L_Lp_bull : ∀S.∀e:re S.𝐋 e = 𝐋\p (•pre_of_re ? e).
#S e; nrewrite > (bull_cup…); nrewrite > (Lp_pre_of_re…);
nrewrite > (cupC…); nrewrite > (cup0…); nrewrite > (erase_pre_of_reK…); //;
nqed.

nlemma Pext : ∀S.∀f,g:word S → Prop. f = g → ∀w.f w → g w.
#S f g H; nrewrite > H; //; nqed.
 
(* corollary 18 *)
ntheorem bull_true_epsilon : ∀S.∀e:pitem S. \snd (•e) = true ↔ [ ] ∈ |e|.
#S e; @;
##[ #defsnde; nlapply (bull_cup ? e); nchange in match (𝐋\p (•e)) with (?∪?);
    nrewrite > defsnde; #H; 
    nlapply (Pext ??? H [ ] ?); ##[ @2; //] *; //;

STOP

notation > "\move term 90 x term 90 E" 
non associative with precedence 65 for @{move ? $x $E}.
nlet rec move (S: Alpha) (x:S) (E: pitem S) on E : pre S ≝
 match E with
  [ pz ⇒ 〈 ∅, false 〉
  | pe ⇒ 〈 ϵ, false 〉
  | ps y ⇒ 〈 `y, false 〉
  | pp y ⇒ 〈 `y, x == y 〉
  | po e1 e2 ⇒ \move x e1 ⊕ \move x e2 
  | pc e1 e2 ⇒ \move x e1 ⊙ \move x e2
  | pk e ⇒ (\move x e)^⊛ ].
notation < "\move\shy x\shy E" non associative with precedence 65 for @{'move $x $E}.
notation > "\move term 90 x term 90 E" non associative with precedence 65 for @{'move $x $E}.
interpretation "move" 'move x E = (move ? x E).

ndefinition rmove ≝ λS:Alpha.λx:S.λe:pre S. \move x (\fst e).
interpretation "rmove" 'move x E = (rmove ? x E).

nlemma XXz :  ∀S:Alpha.∀w:word S. w ∈ ∅ → False.
#S w abs; ninversion abs; #; ndestruct;
nqed.


nlemma XXe :  ∀S:Alpha.∀w:word S. w .∈ ϵ → False.
#S w abs; ninversion abs; #; ndestruct;
nqed.

nlemma XXze :  ∀S:Alpha.∀w:word S. w .∈ (∅ · ϵ)  → False.
#S w abs; ninversion abs; #; ndestruct; /2/ by XXz,XXe;
nqed.


naxiom in_move_cat:
 ∀S.∀w:word S.∀x.∀E1,E2:pitem S. w .∈ \move x (E1 · E2) → 
   (∃w1.∃w2. w = w1@w2 ∧ w1 .∈ \move x E1 ∧ w2 ∈ .|E2|) ∨ w .∈ \move x E2.
#S w x e1 e2 H; nchange in H with (w .∈ \move x e1 ⊙ \move x e2);
ncases e1 in H; ncases e2;
##[##1: *; ##[*; nnormalize; #; ndestruct] 
   #H; ninversion H; ##[##1,4,5,6: nnormalize; #; ndestruct]
   nnormalize; #; ndestruct; ncases (?:False); /2/ by XXz,XXze;
##|##2: *; ##[*; nnormalize; #; ndestruct] 
   #H; ninversion H; ##[##1,4,5,6: nnormalize; #; ndestruct]
   nnormalize; #; ndestruct; ncases (?:False); /2/ by XXz,XXze;
##| #r; *; ##[ *; nnormalize; #; ndestruct] 
   #H; ninversion H; ##[##1,4,5,6: nnormalize; #; ndestruct]
   ##[##2: nnormalize; #; ndestruct; @2; @2; //.##]
   nnormalize; #; ndestruct; ncases (?:False); /2/ by XXz;
##| #y; *; ##[ *; nnormalize; #defw defx; ndestruct; @2; @1; /2/ by conj;##]
   #H; ninversion H; nnormalize; #; ndestruct; 
   ##[ncases (?:False); /2/ by XXz] /3/ by or_intror;
##| #r1 r2; *; ##[ *; #defw]
    ...
nqed.

ntheorem move_ok:
 ∀S:Alpha.∀E:pre S.∀a,w.w .∈ \move a E ↔ (a :: w) .∈ E. 
#S E; ncases E; #r b; nelim r;
##[##1,2: #a w; @; 
   ##[##1,3: nnormalize; *; ##[##1,3: *; #; ndestruct; ##| #abs; ncases (XXz … abs); ##]
      #H; ninversion H; #; ndestruct;
   ##|##*:nnormalize; *; ##[##1,3: *; #; ndestruct; ##| #H1; ncases (XXz … H1); ##]
       #H; ninversion H; #; ndestruct;##]
##|#a c w; @; nnormalize; ##[*; ##[*; #; ndestruct; ##] #abs; ninversion abs; #; ndestruct;##]
   *; ##[##2: #abs; ninversion abs; #; ndestruct; ##] *; #; ndestruct;
##|#a c w; @; nnormalize; 
   ##[ *; ##[ *; #defw; nrewrite > defw; #ca; @2;  nrewrite > (eqb_t … ca); @; ##]
       #H; ninversion H; #; ndestruct;
   ##| *; ##[ *; #; ndestruct; ##] #H; ninversion H; ##[##2,3,4,5,6: #; ndestruct]
              #d defw defa; ndestruct; @1; @; //; nrewrite > (eqb_true S d d); //. ##]
##|#r1 r2 H1 H2 a w; @;
   ##[ #H; ncases (in_move_cat … H);
      ##[ *; #w1; *; #w2; *; *; #defw w1m w2m;
          ncases (H1 a w1); #H1w1; #_; nlapply (H1w1 w1m); #good; 
          nrewrite > defw; @2; @2 (a::w1); //; ncases good; ##[ *; #; ndestruct] //.
      ##|
      ...
##|
##|
##]
nqed.


notation > "x ↦* E" non associative with precedence 65 for @{move_star ? $x $E}.
nlet rec move_star (S : decidable) w E on w : bool × (pre S) ≝
 match w with
  [ nil ⇒ E
  | cons x w' ⇒ w' ↦* (x ↦ \snd E)].

ndefinition in_moves ≝ λS:decidable.λw.λE:bool × (pre S). \fst(w ↦* E).

ncoinductive equiv (S:decidable) : bool × (pre S) → bool × (pre S) → Prop ≝
 mk_equiv:
  ∀E1,E2: bool × (pre S).
   \fst E1  = \fst E2 →
    (∀x. equiv S (x ↦ \snd E1) (x ↦ \snd E2)) →
     equiv S E1 E2.

ndefinition NAT: decidable.
 @ nat eqb; /2/.
nqed.

include "hints_declaration.ma".

alias symbol "hint_decl" (instance 1) = "hint_decl_Type1".
unification hint 0 ≔ ; X ≟ NAT ⊢ carr X ≡ nat.

ninductive unit: Type[0] ≝ I: unit.

nlet corec foo_nop (b: bool):
 equiv ?
  〈 b, pc ? (ps ? 0) (pk ? (pc ? (ps ? 1) (ps ? 0))) 〉
  〈 b, pc ? (pk ? (pc ? (ps ? 0) (ps ? 1))) (ps ? 0) 〉 ≝ ?.
 @; //; #x; ncases x
  [ nnormalize in ⊢ (??%%); napply (foo_nop false)
  | #y; ncases y
     [ nnormalize in ⊢ (??%%); napply (foo_nop false)
     | #w; nnormalize in ⊢ (??%%); napply (foo_nop false) ]##]
nqed.

(*
nlet corec foo (a: unit):
 equiv NAT
  (eclose NAT (pc ? (ps ? 0) (pk ? (pc ? (ps ? 1) (ps ? 0)))))
  (eclose NAT (pc ? (pk ? (pc ? (ps ? 0) (ps ? 1))) (ps ? 0)))
≝ ?.
 @;
  ##[ nnormalize; //
  ##| #x; ncases x
       [ nnormalize in ⊢ (??%%);
         nnormalize in foo: (? → ??%%);
         @; //; #y; ncases y
           [ nnormalize in ⊢ (??%%); napply foo_nop
           | #y; ncases y
              [ nnormalize in ⊢ (??%%);
                
            ##| #z; nnormalize in ⊢ (??%%); napply foo_nop ]##]
     ##| #y; nnormalize in ⊢ (??%%); napply foo_nop
  ##]
nqed.
*)

ndefinition test1 : pre ? ≝ ❨ `0 | `1 ❩^* `0.
ndefinition test2 : pre ? ≝ ❨ (`0`1)^* `0 | (`0`1)^* `1 ❩.
ndefinition test3 : pre ? ≝ (`0 (`0`1)^* `1)^*.


nlemma foo: in_moves ? [0;0;1;0;1;1] (ɛ test3) = true.
 nnormalize in match test3;
 nnormalize;
//;
nqed.

(**********************************************************)

ninductive der (S: Type[0]) (a: S) : re S → re S → CProp[0] ≝
   der_z: der S a (z S) (z S)
 | der_e: der S a (e S) (z S)
 | der_s1: der S a (s S a) (e ?)
 | der_s2: ∀b. a ≠ b → der S a (s S b) (z S)
 | der_c1: ∀e1,e2,e1',e2'. in_l S [] e1 → der S a e1 e1' → der S a e2 e2' →
            der S a (c ? e1 e2) (o ? (c ? e1' e2) e2')
 | der_c2: ∀e1,e2,e1'. Not (in_l S [] e1) → der S a e1 e1' →
            der S a (c ? e1 e2) (c ? e1' e2)
 | der_o: ∀e1,e2,e1',e2'. der S a e1 e1' → der S a e2 e2' →
    der S a (o ? e1 e2) (o ? e1' e2').

nlemma eq_rect_CProp0_r:
 ∀A.∀a,x.∀p:eq ? x a.∀P: ∀x:A. eq ? x a → CProp[0]. P a (refl A a) → P x p.
 #A; #a; #x; #p; ncases p; #P; #H; nassumption.
nqed.

nlemma append1: ∀A.∀a:A.∀l. [a] @ l = a::l. //. nqed.

naxiom in_l1: ∀S,r1,r2,w. in_l S [ ] r1 → in_l S w r2 → in_l S w (c S r1 r2).
(* #S; #r1; #r2; #w; nelim r1
  [ #K; ninversion K
  | #H1; #H2; napply (in_c ? []); //
  | (* tutti casi assurdi *) *)

ninductive in_l' (S: Type[0]) : word S → re S → CProp[0] ≝
   in_l_empty1: ∀E.in_l S [] E → in_l' S [] E 
 | in_l_cons: ∀a,w,e,e'. in_l' S w e' → der S a e e' → in_l' S (a::w) e.

ncoinductive eq_re (S: Type[0]) : re S → re S → CProp[0] ≝
   mk_eq_re: ∀E1,E2.
    (in_l S [] E1 → in_l S [] E2) →
    (in_l S [] E2 → in_l S [] E1) →
    (∀a,E1',E2'. der S a E1 E1' → der S a E2 E2' → eq_re S E1' E2') →
      eq_re S E1 E2.

(* serve il lemma dopo? *)
ntheorem eq_re_is_eq: ∀S.∀E1,E2. eq_re S E1 E2 → ∀w. in_l ? w E1 → in_l ? w E2.
 #S; #E1; #E2; #H1; #w; #H2; nelim H2 in E2 H1 ⊢ %
  [ #r; #K (* ok *)
  | #a; #w; #R1; #R2; #K1; #K2; #K3; #R3; #K4; @2 R2; //; ncases K4;

(* IL VICEVERSA NON VALE *)
naxiom in_l_to_in_l: ∀S,w,E. in_l' S w E → in_l S w E.
(* #S; #w; #E; #H; nelim H
  [ //
  | #a; #w'; #r; #r'; #H1; (* e si cade qua sotto! *)
  ]
nqed. *)

ntheorem der1: ∀S,a,e,e',w. der S a e e' → in_l S w e' → in_l S (a::w) e.
 #S; #a; #E; #E'; #w; #H; nelim H
  [##1,2: #H1; ninversion H1
     [##1,8: #_; #K; (* non va ndestruct K; *) ncases (?:False); (* perche' due goal?*) /2/
     |##2,9: #X; #Y; #K; ncases (?:False); /2/
     |##3,10: #x; #y; #z; #w; #a; #b; #c; #d; #e; #K; ncases (?:False); /2/
     |##4,11: #x; #y; #z; #w; #a; #b; #K; ncases (?:False); /2/
     |##5,12: #x; #y; #z; #w; #a; #b; #K; ncases (?:False); /2/
     |##6,13: #x; #y; #K; ncases (?:False); /2/
     |##7,14: #x; #y; #z; #w; #a; #b; #c; #d; #K; ncases (?:False); /2/]
##| #H1; ninversion H1
     [ //
     | #X; #Y; #K; ncases (?:False); /2/
     | #x; #y; #z; #w; #a; #b; #c; #d; #e; #K; ncases (?:False); /2/
     | #x; #y; #z; #w; #a; #b; #K; ncases (?:False); /2/
     | #x; #y; #z; #w; #a; #b; #K; ncases (?:False); /2/
     | #x; #y; #K; ncases (?:False); /2/
     | #x; #y; #z; #w; #a; #b; #c; #d; #K; ncases (?:False); /2/ ]
##| #H1; #H2; #H3; ninversion H3
     [ #_; #K; ncases (?:False); /2/
     | #X; #Y; #K; ncases (?:False); /2/
     | #x; #y; #z; #w; #a; #b; #c; #d; #e; #K; ncases (?:False); /2/
     | #x; #y; #z; #w; #a; #b; #K; ncases (?:False); /2/
     | #x; #y; #z; #w; #a; #b; #K; ncases (?:False); /2/
     | #x; #y; #K; ncases (?:False); /2/
     | #x; #y; #z; #w; #a; #b; #c; #d; #K; ncases (?:False); /2/ ]
##| #r1; #r2; #r1'; #r2'; #H1; #H2; #H3; #H4; #H5; #H6;

*)