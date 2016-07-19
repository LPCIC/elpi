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

include "basics/lists/list.ma".

axiom alpha : Type[0].
notation "𝔸" non associative with precedence 90 for @{'alphabet}.
interpretation "set of names" 'alphabet = alpha.

inductive tp : Type[0] ≝ 
| top : tp
| arr : tp → tp → tp.
inductive tm : Type[0] ≝ 
| var : nat → tm
| par :  𝔸 → tm
| abs : tp → tm → tm
| app : tm → tm → tm.

let rec Nth T n (l:list T) on n ≝ 
  match l with 
  [ nil ⇒ None ?
  | cons hd tl ⇒ match n with
    [ O ⇒ Some ? hd
    | S n0 ⇒ Nth T n0 tl ] ].

inductive judg : list tp → tm → tp → Prop ≝ 
| t_var : ∀g,n,t.Nth ? n g = Some ? t → judg g (var n) t
| t_app : ∀g,m,n,t,u.judg g m (arr t u) → judg g n t → judg g (app m n) u
| t_abs : ∀g,t,m,u.judg (t::g) m u → judg g (abs t m) (arr t u).

definition Env := list (𝔸 × tp).

axiom vclose_env : Env → list tp.
axiom vclose_tm : Env → tm → tm.
axiom Lam : 𝔸 → tp → tm → tm.
definition Judg ≝ λG,M,T.judg (vclose_env G) (vclose_tm G M) T.
definition dom ≝ λG:Env.map ?? (fst ??) G.

definition sctx ≝ 𝔸 × tm.
axiom swap_tm : 𝔸 → 𝔸 → tm → tm.
definition sctx_app : sctx → 𝔸 → tm ≝ λM0,Y.let 〈X,M〉 ≝ M0 in swap_tm X Y M.

axiom in_list : ∀A:Type[0].A → list A → Prop.
interpretation "list membership" 'mem x l = (in_list ? x l).
interpretation "list non-membership" 'notmem x l = (Not (in_list ? x l)).

axiom in_Env : 𝔸 × tp → Env → Prop.
notation "X ◃ G" non associative with precedence 45 for @{'lefttriangle $X $G}.
interpretation "Env membership" 'lefttriangle x l = (in_Env x l).

let rec FV M ≝ match M with 
  [ par X ⇒ [X]
  | app M1 M2 ⇒ FV M1@FV M2
  | abs T M0 ⇒ FV M0
  | _ ⇒ [ ] ].

(* axiom Lookup : 𝔸 → Env → option tp. *)

(* forma alto livello del judgment
   t_abs* : ∀G,T,X,M,U.
            (∀Y ∉ supp(M).Judg (〈Y,T〉::G) (M[Y]) U) → 
            Judg G (Lam X T (M[X])) (arr T U) *)

(* prima dimostrare, poi perfezionare gli assiomi, poi dimostrarli *)

axiom Judg_ind : ∀P:Env → tm → tp → Prop.
  (∀X,G,T.〈X,T〉 ◃ G → P G (par X) T) → 
  (∀G,M,N,T,U.
    Judg G M (arr T U) → Judg G N T → 
    P G M (arr T U) → P G N T → P G (app M N) U) → 
  (∀G,T1,T2,X,M1.
    (∀Y.Y ∉ (FV (Lam X T1 (sctx_app M1 X))) → Judg (〈Y,T1〉::G) (sctx_app M1 Y) T2) →
    (∀Y.Y ∉ (FV (Lam X T1 (sctx_app M1 X))) → P (〈Y,T1〉::G) (sctx_app M1 Y) T2) → 
    P G (Lam X T1 (sctx_app M1 X)) (arr T1 T2)) → 
  ∀G,M,T.Judg G M T → P G M T.

axiom t_par : ∀X,G,T.〈X,T〉 ◃ G → Judg G (par X) T.
axiom t_app2 : ∀G,M,N,T,U.Judg G M (arr T U) → Judg G N T → Judg G (app M N) U.
axiom t_Lam : ∀G,X,M,T,U.Judg (〈X,T〉::G) M U → Judg G (Lam X T M) (arr T U).

definition subenv ≝ λG1,G2.∀x.x ◃ G1 → x ◃ G2.
interpretation "subenv" 'subseteq G1 G2 = (subenv G1 G2).

axiom daemon : ∀P:Prop.P.

theorem weakening : ∀G1,G2,M,T.G1 ⊆ G2 → Judg G1 M T → Judg G2 M T.
#G1 #G2 #M #T #Hsub #HJ lapply Hsub lapply G2 -G2 change with (∀G2.?)
@(Judg_ind … HJ)
[ #X #G #T0 #Hin #G2 #Hsub @t_par @Hsub //
| #G #M0 #N #T0 #U #HM0 #HN #IH1 #IH2 #G2 #Hsub @t_app2
  [| @IH1 // | @IH2 // ]
| #G #T1 #T2 #X #M1 #HM1 #IH #G2 #Hsub @t_Lam @IH 
  [ (* trivial property of Lam *) @daemon 
  | (* trivial property of subenv *) @daemon ]
]
qed.

(* Serve un tipo Tm per i termini localmente chiusi e i suoi principi di induzione e
   ricorsione *)