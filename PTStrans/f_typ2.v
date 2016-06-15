(** * Here will we do some more advanced stuff with typing.*)
Require Import f_term f_env f_typ.
Require Import ut_term ut_red ut_env ut_typ ut_sr.
Require Import base.
Require Import List.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt Le Gt Plus Minus.

Module f_typ2_mod (X:term_sig) (Y:pts_sig X) (TM: f_term_mod X) (EM: f_env_mod X TM) 
(UTM: ut_term_mod X) (URM:ut_red_mod X UTM) (UEM:ut_env_mod X UTM) (SRM: ut_sr_mod X Y UTM UEM URM).
 Import UTM URM UEM SRM X Y TM EM .
Include (f_typ_mod  X Y TM EM).

Open Scope F_scope.

Reserved Notation "'ε'  x" (at level 4).
Reserved Notation "'εc' x" (at level 4).

(** In this file we prove more things about judgements
 -An alternative substitution lemma
 -Many facts about the erasure map, including the theorem PTSF -> PTS, erasure injectivity, erasure map for contexts and context conversion
 -The definition of repeated substitution to prove `equality_subst´*)


Lemma subst_typR : forall Δ A1 A2 n Γ Γ1 Γ2 H s,ins_in_env Δ A2 (S n) Γ Γ1->
                 sub_in_env (A2::Δ) (#0 ∽ H ↑h 1) (A1↑1) n Γ1 Γ2 -> Γ ⊣ -> Δ ⊢ A2:!s -> exists t, A2::Δ ⊢ A1↑1 : !t.
intros.
eapply wf_item;[eapply subst_item| |eapply subst_trunc];try eassumption.
destruct weakening as (_&_&HH);eapply HH;[eassumption|eassumption..].
Qed.

Lemma subst_typ : forall Δ A1 A2 n Γ Γ1 Γ2 M N H s, Γ ⊢ M:N->Δ ⊢ H : A2=A1->Δ ⊢ A2:!s
                    ->ins_in_env Δ A2 (S n) Γ Γ1->sub_in_env (A2::Δ) (#0 ∽ H ↑h 1) (A1↑1) n Γ1 Γ2->
                      Γ2 ⊢ (M ↑ 1 # (S n)) [n ← #0 ∽ H ↑h 1] : (N ↑ 1 # (S n)) [n ← #0 ∽ H ↑h 1].
intros.
assert (Γ1 ⊣) by (destruct weakening as (_&_&HH);eapply HH;[eapply wf_typ;eexact H0|eassumption..]).
edestruct subst_typR as (?s&?);try eapply wf_typ;[eassumption..|].
eapply substitution;[eapply weakening;eassumption| |eassumption..].
eapply cConv with (s:=s0).
repeat econstructor;eassumption.
eassumption.
eapply thinning_h;eassumption.
Qed.

Lemma subst_wf : forall Δ A1 A2 n Γ Γ1 Γ2 H s, Γ ⊣->Δ ⊢ H : A2=A1->Δ ⊢ A2:!s
                    ->ins_in_env Δ A2 (S n) Γ Γ1->sub_in_env (A2::Δ) (#0 ∽ H ↑h 1) (A1↑1) n Γ1 Γ2->
                      Γ2 ⊣.
intros.
assert (Γ1 ⊣) by (destruct weakening as (_&_&HH);eapply HH;[eexact H0|eassumption..]).
edestruct subst_typR as (?s&?);[eassumption..|].
eapply substitution;[eexact H5| |eassumption..].
eapply cConv with (s:=s0).
repeat econstructor;eassumption.
eassumption.
eapply thinning_h;eassumption.
Qed.

Lemma subst_eq : forall Δ A1 A2 n Γ Γ1 Γ2 H2 M N H s, Γ ⊢ H2 : M=N->Δ ⊢ H : A2=A1->Δ ⊢ A2:!s
                 ->ins_in_env Δ A2 (S n) Γ Γ1->sub_in_env (A2::Δ) (#0 ∽ H ↑h 1) (A1↑1) n Γ1 Γ2->
                 Γ2 ⊢ (H2 ↑h 1 # (S n)) [n ←h #0 ∽ H ↑h 1] : (M ↑ 1 # (S n)) [n ← #0 ∽ H ↑h 1] = (N ↑ 1 # (S n)) [n ← #0 ∽ H ↑h 1].
intros.
assert (Γ1 ⊣) by (edestruct equality_typing as ((?&?)&_);[eapply H0|];
                  destruct weakening as (_&_&HH);eapply HH;[eapply wf_typ;eassumption|try eassumption..]).
assert (exists s, A2::Δ ⊢ A1↑1 : !s) as (?s&?) by (eapply wf_item;[eapply subst_item| |eapply subst_trunc];eassumption).
eapply substitution;[eapply weakening;eassumption| |eassumption..].
eapply cConv with (s:=s0).
repeat econstructor;eassumption.
eassumption.
eapply thinning_h;eassumption.
Qed.

(**The definition of the erasure map. Since the character | already has a built-in meaning
in Coq, we write ε T for |T|, the erasure map applied to T*)

Fixpoint erasure (T:TM.Term) {struct T} : UTM.Term := match T with
   | # x => (# x)%UT
   | ! s => (! s)%UT
   | M · N =>  ((ε M) · (ε N))%UT
   | Π ( A ), B => (Π (ε A), (ε B))%UT
   | λ [ A ], M => (λ [ε A], (ε M))%UT
   | A ∽ H => ε A
   | Id A u v => (UTM.Id (ε A) (ε u) (ε v))%UT
   | Rfl A u => (refl (ε A) (ε u))%UT
   | J A C b u v p => (UTM.J (ε A) (ε C) (ε b) (ε u) (ε v) (ε p))%UT
 end
   where "'ε' t" := (erasure t) : F_scope.

Fixpoint erasure_context (Γ:EM.Env) {struct Γ} : UEM.Env := match Γ with
   | nil => nil
   | A::Γ => ε A::εc Γ
 end
   where "'εc' t" := (erasure_context t) : F_scope.

Lemma erasure_lift : forall a n m, ε(a ↑ n # m)=(ε a ↑ n # m)%UT.
induction a;simpl;intros;[destruct (le_gt_dec m v);simpl;reflexivity|try rewrite IHa1;try rewrite IHa2;trivial..].
Admitted.

Lemma erasure_subst : forall a n N, ε(a [n ← N])=(ε a [n ← ε N])%UT.
induction a;simpl;intros; [destruct (lt_eq_lt_dec v n) as [[]|];
simpl;try rewrite erasure_lift;trivial|try rewrite IHa1;try rewrite IHa2;trivial..].
Admitted.

Hint Rewrite erasure_lift erasure_subst.

Lemma erasure_lem2 : forall H a, ε a = ε((a ↑ 1 # 1) [ ← #0 ∽ H]).
intros; rewrite erasure_subst. change (ε(#0 ∽ H)) with (ε(#0)). rewrite <- erasure_subst.
rewrite_l_rev erasure_lem1;reflexivity.
Qed.

Lemma erasure_item : forall Γ A v, A ↓ v ∈ Γ -> (ε A ↓ v ∈ εc Γ)%UT.
induction 1;simpl;auto.
Qed.

Lemma erasure_item_lift : forall Γ A v, A ↓ v ⊂ Γ -> (ε A ↓ v ⊂ εc Γ)%UT.
destruct 1 as (?&?&?). exists ε x;intuition. rewrite <- erasure_lift; rewrite <- H; reflexivity.
apply erasure_item;assumption.
Qed.

Lemma erasure_item_lift_rev : forall Δ Γ v A, εc Γ = Δ->(A ↓ v ⊂ Δ)%UT->exists A',ε A'=A/\ A' ↓ v ⊂ Γ.
induction Δ;destruct 2 as (?&?&?);subst. 
inversion H1.
destruct Γ;try discriminate;simpl in H;injection H;intros;subst.
inversion H1;subst.
exists t↑1;split. rewrite erasure_lift;reflexivity. exists t;intuition.
edestruct IHΔ as (?&?&?&?&?);[reflexivity|exists x;eauto|subst].
exists x1↑(S (S n)). rewrite erasure_lift in *. apply UTM.inv_lift in H0.
rewrite H0;intuition. exists x1;intuition.
Qed.

(**This Theorem proves that if a judgement is true in PTSF, 
the erasure of the judgement is true in normal PTS*)
Theorem PTSF2PTS : (forall Γ A B,Γ ⊢ A : B -> (εc Γ ⊢ ε A : ε B)%UT )/\
                   (forall Γ H A B, Γ ⊢ H : A = B -> ε A ≡ ε B)/\
                   (forall Γ, Γ ⊣-> εc Γ ⊣ %UT).
(* apply typ_induc;simpl;intros;trivial;try (econstructor;eassumption). *)
(* (*typ*) *)
(* constructor;try apply erasure_item_lift;trivial. *)
(* rewrite erasure_subst. econstructor;eassumption. *)
(* (*eq*) *)
(* apply Betac_sym;trivial. *)
(* apply Betac_trans with ε B;trivial. *)
(* apply Betac_Betas;apply Betas_Beta;rewrite erasure_subst;simpl;constructor. *)
(* simpl;apply Betac_Pi;rewrite <- erasure_lem2 in H5;assumption.  *)
(* simpl;apply Betac_La;rewrite <- erasure_lem2 in H7;assumption.  *)
(* simpl;apply Betac_App;assumption. *)
(* Qed. *)
Admitted.

(**Here we prove the `injectivity´ of the erasure map*)
Proposition erasure_injectivity_term : forall a b Γ A B,Γ ⊢ a : A->Γ ⊢ b : B->ε a=ε b->exists H, Γ ⊢ H : a = b.
(* induction a; *)
(* [(induction b;simpl;intros;try discriminate;try (inversion H0;subst;edestruct IHb;eauto)).. *)
(* |intros; apply gen_conv in H; destruct H as (A0&s&?&?&?); *)
(* destruct (IHa b Γ A0 B);trivial;exists (ι(a∽p)†•x);eauto]. *)
(* (*var*) *)
(* injection H1;intros;subst; exists (ρ #v0);eauto. *)
(* (*sort*) *)
(* injection H1;intros;subst; exists (ρ !s0);eauto. *)
(* (*prod*) *)
(* injection H1;intros.  *)
(* apply gen_pi in H; apply gen_pi in H0. *)
(* destruct H as (s&t&u&?&?&?&?);destruct H0 as (s'&t'&u'&?&?&?&?). *)
(* destruct (IHa1 b1 Γ !s !s');try eassumption. *)
(* destruct (IHa2 ((b2 ↑ 1 # 1) [ ← #0 ∽ x ↑h 1]) (a1 :: Γ) !t !t'). eassumption. *)
(* change !t' with (!t' ↑ 1 # 1) [ ← #0 ∽ x ↑h 1]. eapply subst_typ;try eassumption;repeat econstructor;eassumption. *)
(* rewrite <- erasure_lem2;assumption. *)
(* econstructor; eapply cProdEq; [eexact H4|eexact H7|eassumption..]. *)
(* (*abs*) *)
(* injection H1;intros.  *)
(* apply gen_la in H; apply gen_la in H0. *)
(* destruct H as (s&t&u&B0&?&?&?&?&?);destruct H0 as (s'&t'&u'&B1&?&?&?&?&?). *)
(* destruct (IHa1 b1 Γ !s !s');try eassumption. *)
(* destruct (IHa2 ((b2 ↑ 1 # 1) [ ← #0 ∽ x ↑h 1]) (a1 :: Γ) B0 (B1 ↑ 1 # 1) [ ← #0 ∽ x ↑h 1]). eassumption. *)
(* eapply subst_typ;try eassumption;repeat econstructor;eassumption. *)
(* rewrite <- erasure_lem2;assumption. *)
(* econstructor; eapply cAbsEq; [eexact H4|eexact H8|eassumption..]. *)
(* (*app*) *)
(* injection H1;intros.  *)
(* apply gen_app in H; apply gen_app in H0. *)
(* destruct H as (A0&B0&?&?&?);destruct H0 as (A1&B1&?&?&?). *)
(* destruct (IHa1 b1 Γ (Π (A0), B0) (Π (A1), B1));try eassumption. *)
(* destruct (IHa2 b2 Γ A0 A1);trivial. *)
(* econstructor; eapply cAppEq;eassumption. *)
(* Qed. *)
Admitted.

Lemma erasure_injectivity_term_sort : forall A Γ B s,Γ ⊢ A : B->ε A=!s%UT->Γ ⊢ A = !s.
induction A;simpl;intros;try discriminate.
injection H0;intros;subst;econstructor;eapply cRefl;eassumption.
inversion H;intros;subst.
edestruct IHA;try eassumption;econstructor;eapply cTrans with (B:=A);apply cSym. 
eapply cIota;eassumption. apply cSym;eassumption.
Qed.

Lemma erasure_injectivity_term_type : forall A' A Γ a,Γ ⊢ a : A'->forall B,Γ ⊢ A : B->ε A=ε A'->Γ ⊢ A = A'.
intros. apply TypeCorrect in H; destruct H as [(?&?)|(?&?)]. 
subst; eapply erasure_injectivity_term_sort;eassumption.
intros;eapply erasure_injectivity_term;eassumption.
Qed.

Lemma erasure_injectivity_type : forall A1 A2 Γ B1 B2,Γ ⊢ B1 : A1->Γ ⊢ B2 : A2->ε A1=ε A2
                                 ->((A1=A2/\exists s,A1=!s)\/Γ ⊢ A1 = A2).
intros;destruct (TypeCorrect Γ B1 A1 H) as [(?&?)|(?&?)].
apply TypeCorrect in H0 as [(?&?)|(?&?)].
left;subst;simpl in H1;subst. injection H1;intros;subst. eauto. 
edestruct erasure_injectivity_term_type;[exact H|exact H0|symmetry;assumption|].
right;econstructor;apply cSym;eassumption.
right;eapply erasure_injectivity_term_type;eassumption.
Qed.

Lemma erasure_term : forall A1 A2 Γ a1,Γ ⊢ a1 : A1->ε A1=ε A2->semitype A2 Γ->exists a2,ε a2=ε a1/\Γ ⊢ a2 : A2.
destruct 3 as [(?&?)|(?&?)].
destruct (TypeCorrect _ _ _ H) as [(?&?)|(?&?)].
subst;simpl in H0;injection H0;intros;subst. exists a1;eauto.
subst;simpl in H0.
destruct (erasure_injectivity_term_sort _ _ _ x H2); try assumption.
edestruct equality_typing as (?&?&?); try exact H1.
destruct (gen_sort _ _ _ H4) as (?&?&?);subst.
exists (a1 ∽ x1);eauto.
destruct (erasure_injectivity_term_type _ _ _ _ H _ H1);try (symmetry;assumption).
exists (a1 ∽ x0†);eauto.
Qed.

Lemma erasure_term_type : forall Γ a1 A1 A2 B s,Γ ⊢ a1 : A1->Γ ⊢ A2 : B->ε A1=ε A2->ε B=!s%UT
                            ->exists A a,ε A=ε A1/\ε a=ε a1/\Γ ⊢ a : A : !s.
intros. change !s%UT with (ε!s) in H2. edestruct erasure_term as (A&?&?);[exact H0|exact H2|left;exists s;trivial|].
 edestruct erasure_term as (a&?&?). exact H. transitivity (ε A2). exact H1. symmetry;exact H3.
right;exists s;trivial.
exists A;exists a;intuition. transitivity (ε A2);intuition.
Qed.

Lemma erasure_equality : forall Γ a1 a2 A B H,Γ ⊢ H : a1 = a2->Γ ⊢ a1 : A->Γ ⊢ a2 : A->ε A=ε B->semitype B Γ
                           ->exists b1 b2,ε b1=ε a1/\ε b2=ε a2/\Γ ⊢ b1 : B/\Γ ⊢ b2 : B/\Γ ⊢ b1 = b2.
intros. edestruct erasure_term as (b1&?&?);[exact H1|exact H3|assumption| ].
edestruct erasure_term as (b2&?&?);[exact H2|exact H3|assumption| ].
exists b1;exists b2;intuition.
eapply erasure_injectivity_term in H5;eauto. eapply erasure_injectivity_term in H7;eauto.
destruct H5;destruct H7.
econstructor;eapply cTrans. exact H5.
eapply cTrans. exact H0. eapply cSym;exact H7.
Qed.

Lemma erasure_equality2 : forall Γ a1 a2 b1 b2 B1 B2 H,Γ ⊢ H : a1 = a2->Γ ⊢ b1 : B1->Γ ⊢ b2 : B2->ε a1=ε b1->ε a2=ε b2
                           ->Γ ⊢ b1 = b2.
intros. 
edestruct equality_typing as ((?&?)&(?&?));[exact H0|].
destruct (erasure_injectivity_term _ _ _ _ _ H5 H1 H3) as (?&?).
destruct (erasure_injectivity_term _ _ _ _ _ H6 H2 H4) as (?&?).
econstructor;eapply cTrans;[eapply cSym;eexact H7|eapply cTrans;[eexact H0|eexact H8]].
Qed.

(** This is a map which erases only the outer conversion in a term. It will be used in the following situation:
Suppose ε T=Π(A'),B', then we can write T as (Π(A),B)∽H1∽H2∽...∽Hn. Using the outer erasure, we can retrieve A and B from T.*)
Fixpoint erasure_outer (T:TM.Term) {struct T} : TM.Term := match T with
   | # x => # x
   | ! s => ! s
   | M · N =>  M · N
   | Π ( A ), B => Π (A), B
   | λ [ A ], M => λ [A], M
   | A ∽ H => erasure_outer A
   | Id A u v => Id A u v
   | Rfl A u => Rfl A u
   | J A C b u v p => J A C b u v p
 end.

Lemma erasure_erasure_outer : forall t,ε (erasure_outer t)=ε t.
induction t;simpl;try reflexivity;assumption.
Qed.

Lemma erasure_outer_not_conv : forall t a H,~(erasure_outer t=a∽H).
induction t;intros;simpl;try discriminate;trivial.
Qed.

Lemma erasure_outer_typing : forall Γ A B,Γ ⊢ A : B->exists B',Γ ⊢ erasure_outer A : B'.
induction 1;simpl;try assumption;econstructor;econstructor;eassumption.
Qed.

Lemma context_conversion_context : forall Γ Δ v A, εc Γ = εc Δ->A ↓ v ⊂ Γ->exists A',ε A'=ε A/\ A' ↓ v ⊂ Δ.
induction Γ;destruct 2 as (?&?&?). 
inversion H1.
simpl in H;destruct Δ;try discriminate;simpl in H;injection H;intros;subst.
inversion H1;subst.
exists t↑1;split. rewrite 2 erasure_lift;f_equal;symmetry;trivial. exists t;intuition.
edestruct IHΓ as (?&?&?&?&?);[exact H2|exists x;eauto|..].
subst. exists x1↑(S (S n)). rewrite 2 erasure_lift in *. apply UTM.inv_lift in H0.
rewrite H0;intuition. exists x1;intuition.
Qed.


(** some destruction tactics for the Theorem context_conversion*)

Local Ltac destruct_ext := fun H Γ A =>
let t := fresh "t" with x := fresh "x" with T := fresh "T" with Ht := fresh "Ht" with HT := fresh "HT" 
with eq1 := fresh "eqt" with eq2 := fresh "eq" with eq3 := fresh "eqT" in
(edestruct H with (Δ:=Γ) as (t&x&eq1&eq2&Ht);
[try assumption;econstructor;eassumption|try assumption;simpl;f_equal;trivial;symmetry;trivial|];
try match goal with
 | [ H0 : ε A = _ |- _ ] => symmetry in eq2;apply (eq_trans H0) in eq2
end;
edestruct erasure_term with (A2:=A) as (T&eq3&HT);[exact Ht|eauto|try (left;eauto;fail);try (right;eauto;fail)| ];
try (apply (eq_trans eq3) in eq1; clear eq3 eq2 x Ht t)
).

Local Ltac destruct_ext2 := fun H Γ =>
let x := fresh "x" with T := fresh "T" with HT := fresh "HT" with eq1 := fresh "eqt" with eq2 := fresh "eq" in
(edestruct H with (Δ:=Γ) as (T&x&eq1&eq2&HT);
[try assumption;econstructor;eassumption|try assumption;simpl;f_equal;trivial;symmetry;trivial|]
).

Local Ltac destruct_eq := fun H Γ =>
let A := fresh "A" with B := fresh "B" with HAB := fresh "H" with HT := fresh "HT" with eq1 := fresh "eqA" with eq2 := fresh "eqB"
with tp1 := fresh "tp" with Htp1 := fresh "Htp" with HH1 := fresh "HH" with HHT1 := fresh "HHT" in
(edestruct H with (Δ:=Γ) as (HAB&A&B&eq1&eq2&HT);
[try assumption;econstructor;eassumption|try assumption;simpl;f_equal;trivial;symmetry;trivial|];
try match goal with
 | [ H0 : ε ?a = ε ?b, eq1 : ε A = ε ?b  |- _ ] => rewrite <- H0 in eq1;
 destruct (equality_typing _ _ _ _ HT) as ((tp1&Htp1)&_);
 try match goal with
  | H1 : (_ ⊢ a : _) |- _ => edestruct erasure_injectivity_term      as (HH1&HHT1);[exact H1|exact Htp1|symmetry;assumption| ]
  | H1 : (_ ⊢ _ : a) |- _ => edestruct erasure_injectivity_term_type as (HH1&HHT1);[exact H1|exact Htp1|assumption| ];apply cSym in HHT1
 end;try apply (cTrans _ _ _ _ _ _ HHT1) in HT; clear tp1 Htp1 HHT1 A eq1
end;let tp2 := fresh "tp" with Htp2 := fresh "Htp" with HH2 := fresh "HH" with HHT2 := fresh "HHT" in
try match goal with
 | [ H0 : ε ?a = ε ?b, eq2 : ε B = ε ?b  |- _ ] => rewrite <- H0 in eq2;
 destruct (equality_typing _ _ _ _ HT) as (_&(tp2&Htp2));
 try match goal with
  | H1 : (_ ⊢ a : _) |- _ => edestruct erasure_injectivity_term      as (HH2&HHT2);[try exact H1|try exact Htp2|symmetry;try assumption| ]
  | H1 : (_ ⊢ _ : a) |- _ => edestruct erasure_injectivity_term_type as (HH2&HHT2);[exact H1|exact Htp2|assumption| ];apply cSym in HHT2
 end;apply cSym in HT;try apply (cTrans _ _ _ _ _ _ HHT2) in HT;apply cSym in HT;clear tp2 Htp2 HHT2 B eq2
end;match goal with
 | [ HT : (_ ⊢ ?a : _ = _) |- _ ] => revert HT;generalize a;clear HAB;intros HAB HT;try clear HH1;try clear HH2
end
).

Local Ltac search_prod :=
let HeqX := fresh "HeqX" with Htp := fresh "Htp" with Hetp := fresh "Hetp" with s := fresh "s" in
match goal with
 | eq : ε ?x = ε (Π (?A), ?B),HT : _ ⊢ _ : ?x |- _ => 
 rewrite <- erasure_erasure_outer in eq at 1;remember (erasure_outer x) as X eqn:HeqX;
 destruct X;simpl in eq;try discriminate;[|symmetry in HeqX;apply erasure_outer_not_conv in HeqX; elim HeqX];
 destruct (TypeCorrect _ _ _ HT) as [(?&Htp)|(s&Htp)];[subst;simpl in HeqX;discriminate|];
 destruct (erasure_outer_typing _ _ _ Htp) as (?&Hetp);
 rewrite <- HeqX in Hetp;
 destruct (gen_pi _ _ _ _ Hetp) as (?s&_&?s&?&_&?&_);subst;clear s Htp HeqX HT;injection eq;intros
end.

(** Here we prove context conversion. This is a Theorem we do not use in the paper or thesis, but it allows some simpler formulation of the implication PTSeq -> PTSf. *)

Lemma context_conversion : 
(forall Γ   A B,Γ ⊢     A : B->forall Δ,Δ ⊣->εc Γ = εc Δ->exists    A' B',ε A'=ε A/\ε B'=ε B/\Δ ⊢      A' : B')/\
(forall Γ H A B,Γ ⊢ H : A = B->forall Δ,Δ ⊣->εc Γ = εc Δ->exists H' A' B',ε A'=ε A/\ε B'=ε B/\Δ ⊢ H' : A' = B')/\
(forall Γ,      Γ ⊣ ->True).
(* apply typ_induc;intros;trivial. *)
(* (*sort*) *)
(* exists !s;exists !t;intuition. *)
(* (*var*) *)
(* edestruct context_conversion_context as (A0&?&?);[eassumption|exact i|exists #v;exists A0;intuition]. *)
(* (*prod*) *)
(* destruct_ext H Δ !s1. *)
(* destruct_ext H0 (T::Δ) !s2. *)
(* exists (Π (T), T0);exists !s3;simpl;intuition. *)
(* f_equal;assumption. econstructor;eassumption. *)
(* (*abs*) *)
(* destruct_ext H Δ !s1. *)
(* destruct_ext H1 (T::Δ) !s2. *)
(* destruct_ext H0 (T::Δ) T0. *)
(* exists (λ [T], T1);exists (Π (T), T0);simpl;intuition. *)
(* f_equal;assumption. f_equal;assumption. econstructor;eassumption. *)
(* (*app*) *)
(* destruct_ext2 H Δ. search_prod. *)
(* destruct_ext H Δ (Π (X1), X2). simpl;rewrite eq;assumption. *)
(* destruct_ext H0 Δ X1. *)
(* exists (T0 · T1);exists (X2 [ ← T1]);simpl;intuition. *)
(* f_equal;assumption. rewrite 2! erasure_subst;f_equal;assumption. econstructor;eassumption. *)
(* (*conv*) *)
(* destruct_ext2 H0 Δ. *)
(* destruct_ext H1 Δ !s. *)
(* destruct_eq H2 Δ. *)
(* eexists (T ∽ _);exists T0;simpl;intuition. *)
(* econstructor; try eassumption. *)
(* (*refl*) *)
(* destruct_ext2 H Δ. *)
(* do 3 econstructor;eauto. *)
(* (*sym*) *)
(* destruct_eq H0 Δ. *)
(* do 3 econstructor;eauto. *)
(* (*trans*) *)
(* destruct_eq H0 Δ. *)
(* destruct_eq H1 Δ. *)
(* edestruct equality_typing as (?&?&?). exact HT. *)
(* edestruct equality_typing as ((?&?)&?). exact HT0. *)
(* edestruct erasure_injectivity_term;[exact H7|exact H8|transitivity ε B;trivial;symmetry;trivial|]. *)
(* econstructor;exists A0;exists B1;intuition. *)
(* eapply cTrans. exact HT. eapply cTrans.  *)
(* exact H10. exact HT0. *)
(* (*beta*) *)
(* destruct_ext H0 Δ !s1. *)
(* destruct_ext H Δ T. *)
(* destruct_ext H2 (T::Δ) !s2. *)
(* destruct_ext H1 (T::Δ) T1. *)
(* econstructor;exists ((λ [T], T2) · T0);exists (T2 [ ← T0]). *)
(* split. simpl;f_equal;[f_equal|];assumption. *)
(* split. rewrite 2 erasure_subst;f_equal;assumption. *)
(* eapply cBeta;eassumption. *)
(* (*prod-eq*) *)
(* destruct_ext H0 Δ !s1. *)
(* destruct_ext H1 Δ !s1'. *)
(* destruct_ext H2 (T::Δ) !s2. *)
(* destruct_ext H3 (T0::Δ) !s2'. *)
(* destruct_eq  H4 Δ. *)
(* assert (ε ((T2 ↑ 1 # 1) [ ← #0 ∽ H8 ↑h 1])=ε ((B' ↑ 1 # 1) [ ← #0 ∽ H ↑h 1])). *)
(* rewrite 2 erasure_subst;rewrite 2 erasure_lift;f_equal;trivial;f_equal;trivial. *)
(* assert (T::Δ ⊢ ((T2 ↑ 1 # 1) [ ← #0 ∽ H8 ↑h 1]) : ((!s2' ↑ 1 # 1) [ ← #0 ∽ H8 ↑h 1])). *)
(* eapply subst_typ;try eassumption;repeat econstructor. *)
(* destruct_eq  H5 (T::Δ). *)
(* econstructor;exists (Π (T), T1);exists (Π (T0), T2). *)
(* split;[simpl;f_equal;assumption|]. *)
(* split;[simpl;f_equal;assumption|]. *)
(* eapply cProdEq;[exact r|exact r0|eassumption..]. *)
(* (*abs-eq*) *)
(* destruct_ext H0 Δ !s1. *)
(* destruct_ext H1 Δ !s1'. *)
(* destruct_ext H4 (T::Δ) !s2. *)
(* destruct_ext H5 (T0::Δ) !s2'. *)
(* destruct_ext H2 (T::Δ) T1. *)
(* destruct_ext H3 (T0::Δ) T2. *)
(* destruct_eq  H6 Δ. *)
(* assert (ε ((T4 ↑ 1 # 1) [ ← #0 ∽ H10 ↑h 1])=ε ((b' ↑ 1 # 1) [ ← #0 ∽ H ↑h 1])). *)
(* rewrite 2 erasure_subst;rewrite 2 erasure_lift;f_equal;trivial;f_equal;trivial. *)
(* assert (T::Δ ⊢ ((T4 ↑ 1 # 1) [ ← #0 ∽ H10 ↑h 1]) : ((T2 ↑ 1 # 1) [ ← #0 ∽ H10 ↑h 1])). *)
(* eapply subst_typ;try eassumption;repeat econstructor. *)
(* destruct_eq  H7 (T::Δ). *)
(* econstructor;exists (λ [T], T3);exists (λ [T0], T4). *)
(* split;[simpl;f_equal;assumption|]. *)
(* split;[simpl;f_equal;assumption|]. *)
(* eapply cAbsEq;[exact r|exact r0|eassumption..]. *)
(* (*app-eq*) *)
(* destruct_ext2 H0 Δ. search_prod. *)
(* destruct_ext H0 Δ (Π (X1), X2). simpl;rewrite eq;assumption. *)
(* clear eq;destruct_ext H2 Δ X1. *)
(* destruct_ext2 H1 Δ. search_prod. *)
(* destruct_ext H1 Δ (Π (X3), X4). simpl;rewrite eq;assumption. *)
(* clear eq;destruct_ext H3 Δ X3. *)
(* destruct_eq H4 Δ. destruct_eq H5 Δ. *)
(* econstructor;exists (T0 · T1);exists (T3 · T4). *)
(* split;[simpl;f_equal;assumption|]. *)
(* split;[simpl;f_equal;assumption|]. *)
(* eapply cAppEq;eassumption. *)
(* (*iota*) *)
(* destruct_ext2 H0 Δ. *)
(* destruct_ext H1 Δ !s. *)
(* destruct_eq H2 Δ. *)
(* econstructor;exists T;eexists (T ∽ _);intuition. *)
(* eapply cIota;eassumption. *)
(* Qed. *)
Admitted.

(** * Multiple substitutions.*)

(**
We want to prove that if the following assumptions hold
A::Γ ⊢ F : N
Γ ⊢ H : M1 = M2
Γ ⊢ M1 : A
Γ ⊢ M2 : A 
then the following conclusion also holds:
Γ ⊢ F [ ← M1] = F [ ← M2]
Simply proving this by induction on the first assumption does not work,
we need to generalize the context, such that A can be anywhere in the context Γ. 
To let everything work, notation becomes messy.
*) 
Inductive subst_mult_env : nat->Env->list Prf->Env-> Prop :=
| msub_O : forall n Γ,subst_mult_env n Γ nil Γ
| msub_S : forall n Γ H HH Γ' Γs Γ1 Γ2 A1 A2 s, 
subst_mult_env (S n) Γ' HH Γ ->trunc (S n) Γ Γs->
Γs ⊢ A2 : !s -> Γs ⊢ H : A2 = A1 -> ins_in_env Γs A2 (S n) Γ Γ1-> 
sub_in_env (A2::Γs) (#0 ∽ H ↑h 1) (A1↑1) n Γ1 Γ2->
subst_mult_env n  Γ' (H::HH) Γ2.

Fixpoint subst_mult_term (n:nat) (M:Term) (HH:list Prf) {struct HH} := match HH with
| nil => M
| H'::HH' => (subst_mult_term (S n) M  HH') ↑ 1 # (S n) [n ← #0 ∽ H' ↑h 1]
end.

Fixpoint subst_mult_prf (n:nat) (H:Prf) (HH:list Prf) {struct HH} := match HH with
| nil => H
| H'::HH' => (subst_mult_prf (S n) H HH') ↑h 1 # (S n) [n ←h #0 ∽ H' ↑h 1]
end.

Lemma subst_mult_typ : forall n Γ HH Γ' M' N', Γ' ⊢ M' : N' -> subst_mult_env n Γ' HH Γ -> 
                        Γ ⊢ subst_mult_term n M' HH : subst_mult_term n N' HH.
induction 2;simpl.
assumption.
eapply subst_typ;[apply IHsubst_mult_env|..];eassumption.
Qed.

Lemma subst_mult_wf : forall n Γ HH Γ', Γ' ⊣ -> subst_mult_env n Γ' HH Γ -> Γ ⊣.
induction 2;simpl.
assumption.
eapply subst_wf;[apply IHsubst_mult_env|..];eassumption.
Qed.

Lemma subst_mult_eq : forall n Γ HH Γ' H' M' N', Γ' ⊢ H' : M' = N' -> subst_mult_env n Γ' HH Γ 
                        -> Γ ⊢ subst_mult_prf n H' HH : subst_mult_term n M' HH = subst_mult_term n N' HH.
induction 2;simpl.
assumption.
eapply subst_eq;[apply IHsubst_mult_env|..];eassumption.
Qed.

Lemma subst_mult_lift_inf : forall HH n M' i,i<=n->subst_mult_term n M'↑i HH=(subst_mult_term (n-i) M' HH)↑i.
induction HH;intros;simpl.
reflexivity.
rewrite IHHH;[|apply le_trans with n;[assumption|do 2 constructor]].
rewrite <- (le_plus_minus_r i (S n)) at 1;[|constructor;assumption];
rewrite_l liftP2;[|apply le_0_n].
rewrite <- (le_plus_minus_r i n) at 3;[|assumption];
rewrite_l substP2;[|apply le_0_n].
rewrite minus_Sn_m;[reflexivity|assumption].
Qed.

Lemma subst_mult_lift_sup : forall HH n M' i,length HH+n<=i->subst_mult_term n M'↑i HH=M'↑i.
induction HH;intros;simpl in *.
reflexivity.
rewrite IHHH;[|rewrite <- plus_n_Sm;assumption].
assert (S n<=i) by (apply le_trans with (S (length HH + n));[apply le_n_S;apply le_plus_r|assumption]).
rewrite_l liftP3;[|apply le_0_n|simpl;assumption].
rewrite_l substP3;[reflexivity|apply le_0_n|simpl;apply le_trans with (S n);[do 2 constructor|assumption]].
Qed.

Lemma subst_mult_sort : forall HH n s,subst_mult_term n !s HH=!s.
induction HH;intros;simpl;try rewrite IHHH;reflexivity.
Qed.

Lemma subst_mult_var : forall HH v n,n>v->subst_mult_term n #v HH=#v.
induction HH;intros;simpl.
reflexivity.
assert (S n>v). constructor;assumption.
erewrite IHHH;[unfold lift_rec|assumption].
destruct (le_gt_dec (S n) v). destruct (lt_irrefl v).
apply lt_le_trans with (S n);assumption.
unfold subst_rec;destruct (lt_eq_lt_dec v n) as [[]|].
reflexivity.
subst;destruct (lt_irrefl _ H).
destruct (lt_irrefl n);eapply lt_trans;eassumption.
Qed.

Lemma subst_mult_prod : forall HH A B n,subst_mult_term n (Π(A),B) HH=Π(subst_mult_term n A HH),subst_mult_term (S n) B HH.
induction HH;intros;[|simpl;rewrite IHHH];simpl;reflexivity.
Qed.
Lemma subst_mult_abs : forall HH A B n,subst_mult_term n (λ[A],B) HH=λ[subst_mult_term n A HH],subst_mult_term (S n) B HH.
induction HH;intros;[|simpl;rewrite IHHH];simpl;reflexivity.
Qed.
Lemma subst_mult_app : forall HH A B n,subst_mult_term n (A·B) HH=subst_mult_term n A HH·subst_mult_term n B HH.
induction HH;intros;[|simpl;rewrite IHHH];simpl;reflexivity.
Qed.
Lemma subst_mult_conv : forall HH A H n,subst_mult_term n (A∽H) HH=subst_mult_term n A HH∽subst_mult_prf n H HH.
induction HH;intros;[|simpl;rewrite IHHH];simpl;reflexivity.
Qed.

Lemma subst_mult_cons : forall HH n Γ' Γ A', subst_mult_env n Γ' HH Γ->subst_mult_env (S n) (A'::Γ') HH (subst_mult_term n A' HH::Γ).
induction 1;simpl;econstructor;try eassumption;econstructor;eassumption.
Qed.


(** tactic needed for subst_mult_trunc*)

Local Ltac invert :=
repeat match goal with
| H : sub_in_env _ _ _ (S _) _ _ |- _ => inversion H;subst;clear H
| H : sub_in_env _ _ _  0    _ _ |- _ => inversion H;subst;clear H
| H : trunc  0    _ _            |- _ => inversion H;subst;clear H
| H : trunc (S _) _ _            |- _ => inversion H;subst;clear H
| H : ins_in_env _ _ (S _) _ _   |- _ => inversion H;subst;clear H
| H : ins_in_env _ _  0    _ _   |- _ => inversion H;subst;clear H
| H : subst_mult_env _ _ (_::_) _|- _ => inversion H;subst;clear H
| H : subst_mult_env _ _ nil _   |- _ => inversion H;subst;clear H
end;
repeat match goal with
| H : ?x       = ?x       |- _ => clear H
| H : ?x _     = ?x _     |- _ => injection H;intros;subst;clear H
| H : ?x _ _   = ?x _ _   |- _ => injection H;intros;subst;clear H
| H : ?x _ _ _ = ?x _ _ _ |- _ => injection H;intros;subst;clear H
end.

Lemma subst_mult_trunc : forall n Γ HH Γ' A A',subst_mult_env (S n) (A'::Γ') HH (A::Γ) -> subst_mult_env n Γ' HH Γ.
intros.
remember (S n) as n2;remember (A::Γ) as Γ2;remember (A'::Γ') as Γ3;
revert n A A' Γ Γ' Heqn2 HeqΓ2 HeqΓ3.
induction H;intros;subst;invert. econstructor.
econstructor;[eapply IHsubst_mult_env;reflexivity|try eassumption;econstructor;eassumption..].
Qed.

Lemma subst_mult_var_P2 : forall HH v n x,n<=v->v<n+length HH->subst_mult_term n #v HH=#v∽(nth (v-n) HH x)↑h(v+1).
induction HH;intros;simpl in *.
rewrite <- plus_n_O in H0;destruct lt_irrefl with n;apply le_lt_trans with v;assumption.
inversion H. subst. rewrite minus_diag. rewrite subst_mult_var.
unfold lift_rec. destruct le_gt_dec. 
destruct lt_irrefl with v;apply lt_le_trans with (S v);[repeat constructor|assumption].
simpl. destruct lt_eq_lt_dec as [[]|]; try(destruct (lt_irrefl v);assumption).
rewrite_r lift_lift;rewrite (plus_comm v 0);reflexivity.
repeat constructor.
subst. rewrite IHHH with (x:=x);[|apply le_n_S; assumption|rewrite plus_Snm_nSm;assumption].
assert (forall a b,b<=a->(#a ∽ (nth (a - b) HH x) ↑h (a + 1)) ↑ 1 # b=(#0 ∽ (nth (a - b) HH x) ↑h 1)↑(S a)) by
(intros;simpl;destruct le_gt_dec;[rewrite <- plus_n_O;rewrite_r lift_lift;rewrite_r liftP3;simpl;
[reflexivity|apply le_0_n|rewrite plus_comm;constructor;assumption]|
destruct (lt_irrefl b);apply le_lt_trans with a0;assumption]).
rewrite H2;[|apply le_n_S; assumption]. 
rewrite_l substP3;[rewrite <- (minus_Sn_m m n);[|assumption]|apply le_0_n|assumption].
simpl;rewrite_r lift_lift;rewrite plus_comm;reflexivity.
Qed.

Lemma subst_mult_var_eq : forall HH Γ Δ v n,Δ ⊣ -> n<=v->v<n+length HH->subst_mult_env n Δ HH Γ->Γ ⊢ #v = subst_mult_term n #v HH.
induction HH;intros;simpl in *.
rewrite <- plus_n_O in H1;destruct (lt_irrefl v).
apply lt_le_trans with n;assumption.
inversion H2;subst.
edestruct subst_typR as (?s&?);try eapply subst_mult_wf;try eassumption.
assert (Γ ⊣) by (eapply subst_mult_wf;eassumption).
inversion H12;subst.
inversion H0.
subst;rewrite subst_mult_var;[|constructor]. unfold lift_rec. destruct le_gt_dec.
destruct (lt_irrefl v);apply lt_le_trans with (S v);[constructor|try assumption].
simpl;destruct lt_eq_lt_dec as [[]|];try (destruct (lt_irrefl v);assumption).
assert (trunc (S v) Γ Γs). (change (S v) with (1+v);eapply trunc_trans;[eapply subst_trunc2;eassumption|repeat constructor]).
rewrite_r lift_lift;rewrite plus_comm;simpl.
econstructor. eapply cIota with (s:=s0).
constructor. eassumption. econstructor;repeat split.
eapply nth_sub_sup;try eassumption. constructor. eapply ins_item;eassumption.
change !s0 with !s0↑v. eapply thinning_n;try eassumption. eapply subst_trunc2;eassumption.
rewrite_l lift_lift. rewrite plus_comm;simpl. eapply thinning_n_h;eassumption.
subst.
edestruct IHHH as (?HH&?);[eexact H|eapply le_n_S;eexact H5|rewrite plus_Snm_nSm;assumption|eassumption|].
econstructor.
rewrite (erasure_lem3 n (S m) (#0 ∽ a ↑h 1)) at 1.
eapply subst_eq;eassumption.
apply le_n_S;assumption.
Qed.

(** tactic needed for equality_subst_ext*)

Local Ltac solve :=
try match goal with 
| |- _ ⊢ subst_mult_term ?n _ ?HH : !?s   => replace !s with (subst_mult_term n !s HH) by (apply subst_mult_sort)
| |- _ ⊢ _ : Π(subst_mult_term _ _ _),_   => try rewrite <- subst_mult_prod
| |- _ ⊢ _ : Π(_),(subst_mult_term _ _ _) => try rewrite <- subst_mult_prod
end;
try match goal with 
| |- _ ⊢ subst_mult_term _ _ _ : _ => eapply subst_mult_typ;[|try apply subst_mult_cons;try eassumption]
end;
try match goal with 
| |- _ ⊢ _ [?n←?a] : !?s => change !s with !s[n←a]
| |- _ ⊢ _ : (Π(?A[?n←?a]),?B[S ?n←?a]) => change (Π(A[n←a]),B[S n←a]) with (Π(A),B)[n←a]
end;
try match goal with 
| |- _ ⊢ _ [_←_] : _ => eapply substitution;(eassumption||(econstructor;eassumption)||(eapply wf_typ;eassumption))
end.

Lemma equality_subst_ext : forall Δ Γ' M N a1 a2 T K,Δ ⊢ a1 : T -> Δ ⊢ a2 : T -> Δ ⊢ K : a1 = a2 -> Γ' ⊢ M : N -> 
                            forall Γ1 Γ2 HH, sub_in_env Δ a1 T (length HH) Γ' Γ1->sub_in_env Δ a2 T (length HH) Γ' Γ2
                             ->subst_mult_env 0 Γ2 HH Γ1-> Γ1 ⊢ (M [length HH ← a1]) = subst_mult_term 0 M[length HH ← a2] HH.
(* induction 4;intros;subst;set (n:=length HH) in *. *)
(* (*sort*) *)
(* simpl;rewrite subst_mult_sort.  *)
(* econstructor;eapply cRefl;econstructor;[eassumption|eapply substitution;[eassumption|eexact H|eassumption]]. *)
(* (*var*) *)
(* assert (Γ1 ⊣) by (eapply substitution;[eassumption|eexact H|eassumption]). *)
(* unfold subst_rec;destruct lt_eq_lt_dec as [[]|]. *)
(* eapply subst_mult_var_eq. eapply substitution;[eexact H2|eexact H0|eassumption]. apply le_0_n. simpl;assumption. assumption. *)
(* subst. rewrite subst_mult_lift_sup. *)
(* econstructor;eapply thinning_n_h. eapply subst_trunc2;eassumption. eassumption. eassumption.  *)
(* rewrite plus_comm;constructor. *)
(* destruct H3 as (?&?&?);subst. *)
(* assert (n<=v-1) by (destruct v;[inversion l|change 1 with (1+0);change (S v) with (1+v); *)
(* rewrite <- minus_plus_simpl_l_reverse;rewrite <- minus_n_O;apply le_S_n;assumption]). *)
(* assert (#(v-1)=#(v-1-n)↑n) as eq by (simpl;rewrite <- le_plus_minus;[reflexivity|assumption]). *)
(* rewrite eq;rewrite subst_mult_lift_sup. do 2 econstructor;rewrite <- eq. *)
(* econstructor;[assumption|]. econstructor;repeat split. eapply nth_sub_sup;try eassumption. *)
(* rewrite minus_Sn_m;simpl. rewrite <- minus_n_O;eassumption. *)
(* apply le_lt_trans with n;[apply le_0_n|assumption]. *)
(* unfold n;rewrite plus_comm;simpl;constructor. *)
(* (*prod*) *)
(* simpl;rewrite subst_mult_prod. *)
(* edestruct IHtyp1;[eassumption..|]. *)
(* edestruct IHtyp2 with (HH:=x::HH);simpl;[econstructor;eassumption..| |]. *)
(* eapply msub_S with (s:=s1);[eapply subst_mult_cons;eassumption|do 2 econstructor| *)
(* change !s1 with !s1[n ← a1];eapply substitution;try eassumption;eapply wf_typ;eassumption| *)
(* eassumption|do 2 econstructor|econstructor]. *)
(* econstructor;eapply cProdEq;simpl;try eassumption;solve. *)
(* (*abs*) *)
(* simpl;rewrite subst_mult_abs. *)
(* edestruct IHtyp1;[eassumption..|]. *)
(* edestruct IHtyp2 with (HH:=x::HH);simpl;[econstructor;eassumption..| |]. *)
(* eapply msub_S with (s:=s1);[eapply subst_mult_cons;eassumption|do 2 econstructor| *)
(* change !s1 with !s1[n ← a1];eapply substitution;try eassumption;eapply wf_typ;eassumption| *)
(* eassumption|do 2 econstructor|econstructor]. *)
(* econstructor;eapply cAbsEq;simpl;try eassumption;solve. *)
(* (*app*) *)
(* simpl;rewrite subst_mult_app. *)
(* edestruct IHtyp1;[eassumption..|]. *)
(* edestruct IHtyp2;[eassumption..|]. *)
(* econstructor;eapply cAppEq with (A:=A[n ← a1]) (B:=B[S n ← a1]) (B':=subst_mult_term 1 B [S n ← a2] HH); *)
(* simpl;try eassumption;solve. solve. *)
(* (*conv*) *)
(* simpl;rewrite subst_mult_conv. *)
(* edestruct IHtyp1;[eassumption..|]. *)
(* edestruct IHtyp2;[eassumption..|]. *)
(* econstructor;eapply cTrans. *)
(* apply cSym;eapply cIota with (s:=s);try change !s with !s[n ← a1]; *)
(* eapply substitution;try eassumption;eapply wf_typ;eassumption. *)
(* eapply cTrans. eassumption. *)
(* eapply cIota with (s:=s). *)
(* eapply subst_mult_typ;[|eassumption];eapply substitution;try eassumption;eapply wf_typ;eassumption. *)
(* replace !s with (subst_mult_term 0 !s HH) by (apply subst_mult_sort). *)
(* eapply subst_mult_typ;[|eassumption]. change !s with (!s[n ← a2]). eapply substitution;try eassumption;eapply wf_typ;eassumption. *)
(* eapply subst_mult_eq;[|eassumption]. eapply substitution;try eassumption;eapply wf_typ;eassumption. *)
(* Qed. *)
Admitted.

Corollary equality_subst : forall Γ F N H M1 M2 A,A::Γ ⊢ F : N->Γ ⊢ H : M1 = M2->Γ ⊢ M1 : A->Γ ⊢ M2 : A -> Γ ⊢ F [ ← M1] = F [ ← M2].
intros.
change F[← M2] with (subst_mult_term 0 F[← M2] nil);change 0 with (@length Prf nil).
eapply equality_subst_ext;try eassumption;econstructor;eassumption.
Qed.

(** * Below we prove the result about comparable types and unique derivations *)

Inductive comparable : Term -> Term -> Prop := 
| comp_refl : forall M, comparable M M
| comp_sort : forall s t, comparable !s !t
| comp_prod : forall A M N, comparable M N -> comparable (Π(A),M) (Π(A),N).


Lemma comp_subst : forall M N, comparable M N -> forall a n, comparable M [n ← a] N [n ← a].
induction 1;simpl;constructor;apply IHcomparable.
Qed.

Lemma type_comparable : forall Γ M A, Γ ⊢ M : A -> forall B, Γ ⊢ M : B -> comparable A B.
induction 1;intros ? HH.
apply gen_sort in HH as(?&?&?);subst;constructor.
apply gen_var in HH as(?&?&?);destruct H0 as (?&?&?);destruct H2 as (?&?&?);subst.
assert (x0=x1) by (eapply fun_item;eassumption);subst;constructor.
apply gen_pi in HH as (?&?&?&?&?&?&?);subst;constructor.
apply gen_la in HH as (?&?&?&?&?&?&?&?&?);subst;constructor;apply IHtyp2;assumption.
apply gen_app in HH as (?&?&?&?&?);subst;apply comp_subst.
apply IHtyp1 in H2;inversion H2;[constructor|assumption].
(* apply gen_conv in HH as (?&?&?&?&?). *)
(* edestruct equality_unique;[eexact H2|eexact H5|]. *)
(* subst;constructor. *)
(* Qed. *)
Admitted.

(** We use trees with an arbitrary (finite) number of branches for derivations. We encode the rules by natural numbers.*)

Inductive deriv : Set :=
| node : list deriv -> nat -> deriv.

Import ListNotations.

Inductive der_wf : deriv -> Env -> Prop :=
 | dnil    : der_wf (node nil 0) nil
 | dcons   : forall Γ A s D, der_typ D Γ A !s -> der_wf (node ([D]) 1) (A::Γ)
with der_typ : deriv -> Env -> Term -> Term -> Prop :=
 | dSort   : forall Γ s t D, Ax s t -> der_wf D Γ -> der_typ (node ([D]) 2) Γ !s !t
 | dVar    : forall Γ A v D, A ↓ v ⊂ Γ -> der_wf D Γ -> der_typ (node ([D]) 3) Γ #v A
 | dProd   : forall Γ A B s1 s2 s3 D1 D2, Rel s1 s2 s3 -> der_typ D1 Γ A !s1 -> der_typ D2 (A::Γ) B !s2 -> der_typ (node ([D1;D2]) 4) Γ (Π(A), B) !s3
 | dAbs    : forall Γ A B b s1 s2 s3 D1 D2 D3, Rel s1 s2 s3 -> der_typ D1 Γ A !s1 -> der_typ D2 (A::Γ) b B 
                      -> der_typ D3 (A::Γ) B !s2 -> der_typ (node ([D1;D2;D3]) 5) Γ (λ[A], b) (Π(A), B)
 | dApp    : forall Γ F a A B D1 D2, der_typ D1 Γ F (Π(A), B) -> der_typ D2 Γ a A -> der_typ (node ([D1;D2]) 6) Γ (F · a) (B[←a])
 | dConv   : forall Γ a A B s H D1 D2 D3, der_typ D1 Γ a A -> der_typ D2 Γ B !s -> der_h D3 Γ H A B -> der_typ (node ([D1;D2;D3]) 7) Γ (a ∽ H) B
 | dId     : forall Γ A u v s D1 D2 D3, der_typ D1 Γ A !s -> der_typ D2 Γ u A -> der_typ D3 Γ v A -> der_typ (node ([D1;D2;D3]) 16) Γ (Id A u v) !s
 | dRfl    : forall Γ A u s D1 D2, der_typ D1 Γ A !s -> der_typ D2 Γ u A -> der_typ (node ([D1;D2]) 17) Γ (Rfl A u) (Id A u u)
 | dJ      : forall Γ A C b u v p s t D1 D2 D3 D4 D5 D6,
               der_typ D1 Γ A !s ->
               der_typ D2 Γ C (Π(A), Π(A ↑ 1), Π(Id (A ↑ 2) #1 #0), !t) ->
               der_typ D3 Γ b (Π(A), (C ↑ 1) · #0 · #0 · (Rfl (A ↑ 1) #0)) ->
               der_typ D4 Γ u A ->
               der_typ D5 Γ v A ->
               der_typ D6 Γ p (Id A u v) ->
               der_typ (node ([D1;D2;D3;D4;D5;D6]) 18) Γ (J A C b u p v) (C · u · v · p)
with der_h : deriv -> Env -> Prf -> Term -> Term -> Prop :=
 | dRefl   : forall Γ a A D, der_typ D Γ a A -> der_h (node ([D]) 8) Γ (ρ a) a a
 | dSym    : forall Γ H A B D, der_h D Γ H A B -> der_h (node ([D]) 9) Γ (H†) B A
 | dTrans  : forall Γ H K A B C D1 D2, der_h D1 Γ H A B -> der_h D2 Γ K B C -> der_h (node ([D1;D2]) 10) Γ (H•K) A C
 | dBeta   : forall Γ a A b B s1 s2 s3 D1 D2 D3 D4, Rel s1 s2 s3 -> der_typ D1 Γ a A -> der_typ D2 Γ A !s1
                      -> der_typ D3 (A::Γ) b B -> der_typ D4 (A::Γ) B !s2 -> der_h (node ([D1;D2;D3;D4]) 11) Γ (β((λ[A], b)·a)) ((λ[A], b)·a) (b[←a])
 | dProdEq : forall Γ A A' B B' H K s1 s2 s3 s1' s2' s3' D1 D2 D3 D4 D5 D6, Rel s1 s2 s3 -> Rel s1' s2' s3' 
                      -> der_typ D1 Γ A !s1 -> der_typ D2 Γ A' !s1' -> der_typ D3 (A::Γ) B !s2 -> der_typ D4 (A'::Γ) B' !s2'
                      -> der_h D5 Γ H A A' -> der_h D6 (A::Γ) K B ((B'↑1#1)[←#0∽H↑h1]) 
                      -> der_h (node ([D1;D2;D3;D4;D5;D6]) 12) Γ ({H,[A]K}) (Π(A), B) (Π(A'), B')
 | dAbsEq  : forall Γ A A' b b' B B' H K s1 s2 s3 s1' s2' s3' D1 D2 D3 D4 D5 D6 D7 D8, Rel s1 s2 s3 -> Rel s1' s2' s3' 
                      -> der_typ D1 Γ A !s1 -> der_typ D2 Γ A' !s1' -> der_typ D3 (A::Γ) b B -> der_typ D4 (A'::Γ) b' B' 
                      -> der_typ D5 (A::Γ) B !s2 -> der_typ D6 (A'::Γ) B' !s2' -> der_h D7 Γ H A A' -> der_h D8 (A::Γ) K b ((b'↑1#1)[←#0∽H↑h1]) 
                      -> der_h (node ([D1;D2;D3;D4;D5;D6;D7;D8]) 13) Γ (⟨H,[A]K⟩) (λ[A], b) (λ[A'], b')
 | dAppEq  : forall Γ F F' a a' A A' B B' H K D1 D2 D3 D4 D5 D6, der_typ D1 Γ F (Π(A), B) -> der_typ D2 Γ F' (Π(A'), B') 
                      -> der_typ D3 Γ a A -> der_typ D4 Γ a' A' -> der_h D5 Γ H F F' -> der_h D6 Γ K a a' 
                      -> der_h (node ([D1;D2;D3;D4;D5;D6]) 14) Γ (H ·h K) (F · a) (F' · a')
 | dIota    : forall Γ a A B s H D1 D2 D3, der_typ D1 Γ a A -> der_typ D2 Γ B !s -> der_h D3 Γ H A B -> der_h (node ([D1;D2;D3]) 15) Γ (ι(a∽H)) a (a∽H)
 | dIdEq    : forall Γ A A' u u' v v' s s' HA Hu Hv DA DA' Du Du' Dv Dv' DHA DHu DHv,
                der_typ DA  Γ A  !s    ->
                der_typ DA' Γ A' !s'   ->
                der_typ Du  Γ u  A     ->
                der_typ Du' Γ u' A'    ->
                der_typ Dv  Γ v  A     ->
                der_typ Dv' Γ v' A'    ->
                der_h   DHA Γ HA A  A' ->
                der_h   DHu Γ Hu u  u' ->
                der_h   DHv Γ Hv v  v' ->
                der_h (node ([DA;DA';Du;Du';Dv;Dv';DHA;DHu;DHv]) 19) Γ (IdEq HA Hu Hv) (Id A u v) (Id A' u' v')
 | dRflEq   : forall Γ A A' u u' s s' HA Hu DA DA' Du Du' DHA DHu,
                der_typ DA  Γ A  !s    ->
                der_typ DA' Γ A' !s'   ->
                der_typ Du  Γ u  A     ->
                der_typ Du' Γ u' A'    ->
                der_h   DHA Γ HA A  A' ->
                der_h   DHu Γ Hu u  u' ->
                der_h (node ([DA;DA;Du;Du';DHA;DHu]) 20) Γ (RflEq HA Hu) (Rfl A u) (Rfl A' u')
 | dJEq     : forall Γ A A' C C' b b' u u' v v' p p' s t s' t'
                HA HC Hb Hu Hv Hp
                DA DA' DC DC' Db Db' Du Du' Dv Dv' Dp Dp'
                DHA DHC DHb DHu DHv DHp,
                der_typ DA  Γ A  !s  ->
                der_typ DA' Γ A' !s' ->
                der_typ DC  Γ C  (Π(A), Π(A ↑ 1), Π(Id (A ↑ 2) #1 #0), !t) ->
                der_typ DC' Γ C' (Π(A'), Π(A' ↑ 1), Π(Id (A' ↑ 2) #1 #0), !t') ->
                der_typ Db  Γ b  (Π(A), (C ↑ 1) · #0 · #0 · (Rfl (A ↑ 1) #0)) ->
                der_typ Db' Γ b' (Π(A'), (C' ↑ 1) · #0 · #0 · (Rfl (A' ↑ 1) #0)) ->
                der_typ Du  Γ u  A   ->
                der_typ Du' Γ u' A'  ->
                der_typ Dv  Γ v  A   ->
                der_typ Dv' Γ v' A'  ->
                der_typ Dp  Γ p  (Id A u v)    ->
                der_typ Dp' Γ p' (Id A' u' v') ->
                der_h   DHA Γ HA A A' ->
                der_h   DHC Γ HC C C' ->
                der_h   DHb Γ Hb b b' ->
                der_h   DHu Γ Hu u u' ->
                der_h   DHv Γ Hv v v' ->
                der_h   DHp Γ Hp p p' ->
                der_h (node ([DA;DA';DC;DC';Db;Db';Du;Du';Dv;Dv';Dp;Dp';DHA;DHC;DHb;DHu;DHv;DHp]) 21)
                      Γ
                      (JEq HA HC Hb Hu Hv Hp)
                      (J A  C  b  u  v  p)
                      (J A' C' b' u' v' p')
 | dJRed    : forall Γ A C b u s t DA DC Db Du,
                der_typ DA Γ A !s ->
                der_typ DC Γ C (Π(A), Π(A ↑ 1), Π(Id (A ↑ 2) #1 #0), !t) ->
                der_typ Db Γ b (Π(A), (C ↑ 1) · #0 · #0 · (Rfl (A ↑ 1) #0)) ->
                der_typ Du Γ u A ->
                der_h (node ([DA;DC;Db;Du]) 22) Γ (JRed (J A C b u u (Rfl A u)))
                      (J A C b u u (Rfl A u))
                      (b · u)
.


Scheme der_typ_ind' := Induction for der_typ Sort Prop
 with  der_wf_ind' := Induction for der_wf Sort Prop
 with  der_h_ind' := Induction for der_h Sort Prop.

Combined Scheme der_induc from der_typ_ind', der_h_ind',der_wf_ind'.

Lemma der_complete : (forall Γ   A B, Γ ⊢     A : B -> exists D, der_typ D Γ   A B)/\
                     (forall Γ H A B, Γ ⊢ H : A = B -> exists D, der_h   D Γ H A B)/\
                     (forall Γ      , Γ ⊣           -> exists D, der_wf  D Γ      ).
(* apply typ_induc;intros; *)
(* try match (type of H) with *)
(* | exists _, _ => destruct H *)
(* end; *)
(* try destruct H0;try destruct H1;try destruct H2;try destruct H3;try destruct H4;try destruct H5;try destruct H6;try destruct H7; *)
(* econstructor;try (econstructor;eassumption);(econstructor;[| |eassumption..];eassumption). *)
(* Qed. *)
Admitted.

Lemma der_sound : (forall D Γ   A B, der_typ D Γ   A B -> Γ ⊢     A : B)/\
                  (forall D Γ H A B, der_h   D Γ H A B -> Γ ⊢ H : A = B)/\
                  (forall D Γ      , der_wf  D Γ       -> Γ ⊣          ).
(* apply der_induc;intros;try (econstructor;eassumption);(econstructor;[| |eassumption..];eassumption). *)
(* Qed. *)
Admitted.

Theorem unique_der_ext : (forall D Γ   A B, der_typ D Γ A B   -> forall A0 B0 D0, der_typ D0 Γ A0 B0 -> comparable A A0 -> D = D0)/\
                         (forall D Γ H A B, der_h   D Γ H A B -> forall A0 B0 D0, der_h   D0 Γ H A0 B0                  -> D = D0)/\
                         (forall D Γ      , der_wf  D Γ       -> forall       D0, der_wf  D0 Γ                          -> D = D0).
apply der_induc;intros;
try match goal with
| H : comparable _ _ |- _ => inversion H;subst
end;
try match goal with
| H : der_typ ?D _ _ _   |- _ = ?D => inversion H;subst
| H : der_h   ?D _ _ _ _ |- _ = ?D => inversion H;subst
| H : der_wf  ?D _       |- _ = ?D => inversion H;subst
end;
repeat f_equal;
try (destruct (equality_unique Γ H A A' A A'0) as (_&?);[eapply der_sound;eassumption..|subst]);
try match goal with
| H : forall _, _     ->      ?D = _ |- ?D = _ => eapply H;try eassumption
| H : forall _ _ _, _ ->      ?D = _ |- ?D = _ => eapply H;try eassumption||econstructor
| H : forall _ _ _, _ -> _ -> ?D = _ |- ?D = _ => eapply H;try eassumption||econstructor
end;
try (try (eapply type_comparable;eapply der_sound;eassumption;fail);
try match goal with
| HA : der_h _ ?Γ ?H ?A ?C , HB : der_h _ ?Γ ?H ?B ?D |- comparable ?A ?B => destruct (equality_unique Γ H A C B D);[eapply der_sound;eassumption..|subst;constructor]
| HA : der_h _ ?Γ ?H ?C ?A , HB : der_h _ ?Γ ?H ?D ?B |- comparable ?A ?B => destruct (equality_unique Γ H C A D B);[eapply der_sound;eassumption..|subst;constructor]
end;fail);
[edestruct equality_unique;[eapply der_sound;eexact d4|eapply der_sound;eexact H22|];apply conv_inj in H8;subst;constructor|
edestruct equality_unique;[eapply der_sound;eexact d6|eapply der_sound;eexact H26|];apply conv_inj in H10;subst..];
[constructor|eapply type_comparable;eapply der_sound;eassumption..].
Qed.


Corollary unique_der : (forall D D0 Γ   A B, der_typ D Γ A B   -> der_typ D0 Γ A B   -> D = D0)/\
                     (forall D D0 Γ H A B, der_h   D Γ H A B -> der_h   D0 Γ H A B -> D = D0)/\
                     (forall D D0 Γ      , der_wf  D Γ       -> der_wf  D0 Γ       -> D = D0).
destruct unique_der_ext as (typ&h&wf);repeat split;intros;[eapply typ|eapply h|eapply wf];eassumption||constructor.
Qed.

End f_typ2_mod.
