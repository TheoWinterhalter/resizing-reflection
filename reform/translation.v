Require Import List.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt Le Gt.
Require Omega.

Require Import Coq.Program.Equality.

Require Sorts PTS PTS_Ext.
Module S := PTS_Ext.
Module T := PTS.
Import S T Sorts Sorts.withoutProp.

(* We first would like to express an equivalence between terms that can either
   be in S or in T. If we only look at the terms, then S is included in T. *)
Fixpoint ι (t : S.Term) : Term :=
  match t with
  | S.Var x => #x
  | S.Sort s => !s
  | S.Π A B => Π (ι A) (ι B)
  | S.λ A t => λ (ι A) (ι t)
  | S.App t u => (ι t) · (ι u)
  | S.Σ A B => Σ (ι A) (ι B)
  | S.Pair M N => ⟨ (ι M) , (ι N) ⟩
  | S.π1 M => π1 (ι M)
  | S.π2 M => π2 (ι M)
  | S.Eq A u v => Eq (ι A) (ι u) (ι v)
  | S.refle t => refle (ι t)
  | S.J A P M1 N M2 p => J (ι A) (ι P) (ι M1) (ι N) (ι M2) (ι p)
  end.

(* We also need to define the notion of transport inside T. *)
(* Reserved Notation "p ⋆ t" (at level 30). *)
Definition transport (s : Sorts) (A B p : Term) : Term :=
  λ A (J !s #0 (A ↑) #0 (B ↑) (p ↑)).
(* Notation "p ⋆ a" := ((transport ? ? ? p) · a) *)

Lemma lift_rec0 : forall M n, M ↑ 0 # n = M.
Proof.
  induction M; intros; simpl ;
  try reflexivity ;
  try (rewrite IHM ; reflexivity) ;
  try (rewrite IHM1 ; rewrite IHM2 ; reflexivity) ;
  try (rewrite IHM1 ; rewrite IHM2 ; rewrite IHM3 ; reflexivity).
  - destruct (le_gt_dec n v); reflexivity.
  - rewrite IHM1 ; rewrite IHM2 ; rewrite IHM3 ; rewrite IHM4 ;
    rewrite IHM5 ; rewrite IHM6 ; reflexivity.
  - rewrite IHM1 ; rewrite IHM2 ; rewrite IHM3 ; rewrite IHM4 ;
    reflexivity.
Qed.

Lemma lift0 : forall M, M ↑ 0 = M.
Proof.
  intros; apply lift_rec0.
Qed.

Lemma transport_typ :
  forall Γ s A B p,
    Γ ⊢ A : !s -> Γ ⊢ B : !s ->
    Γ ⊢ p : Eq !s A B ->
    Γ ⊢ transport s A B p : A ⇒ B.
Proof.
  intros Γ s A B p hA hB hp.
  induction s. eapply cλ.
  - exact (Rel0 n n).
  - exact hA.
  - admit. (* Weakening *)
  - cut (
      A :: Γ ⊢ J !(U n) #0 (A ↑) #0 (B ↑) (p ↑) : (#0)[← B ↑]
    ).
    + simpl. rewrite lift0. auto.
    + eapply cJ.
      * { apply cVar.
          - eapply wf_cons. apply cSort.
            + eapply wf_cons. exact hA.
            + apply (Ax0 n (S n)). auto.
          - exists ! (U n) ; split.
              + simpl. auto.
              + apply item_hd.
        }
      * simpl. rewrite lift0.
        { apply cVar.
          - eapply wf_cons. exact hA.
          - exists A ; split ; auto.
        }
      * admit. (* Weakening *)
Admitted.

(* We can now express our relation on T terms. *)
Reserved Notation "t ~ u" (at level 80, no associativity).
Reserved Notation "t ≃ u @ E" (at level 80, no associativity).

(* For the purpose of the proof we define an extension of the relation first. *)
Inductive equiv (E : list (Vars * Vars)) : Term -> Term -> Prop :=
| EquivGen : forall (x y : Vars), In (x,y) E -> #x ≃ #y @ E
| EquivVar : forall (x : Vars), #x ≃ #x @ E
| EquivTL  : forall t1 t2 s A B p,
               t1 ≃ t2 @ E -> (transport s A B p) · t1 ≃ t2 @ E
| EquivTR  : forall t1 t2 s A B p,
               t1 ≃ t2 @ E -> t1 ≃ (transport s A B p) · t2 @ E
| EquivApp : forall t1 t2 u1 u2, t1 ≃ t2 @ E -> u1 ≃ u2 @ E -> t1 · u1 ≃ t2 · u2 @ E
| Equivλ   : forall A1 A2 t1 t2, A1 ≃ A2 @ E -> t1 ≃ t2 @ E -> λ A1 t1 ≃ λ A2 t2 @ E
| EquivΠ   : forall A1 A2 B1 B2, A1 ≃ A2 @ E -> B1 ≃ B2 @ E -> Π A1 B1 ≃ Π A2 B2 @ E
| EquivEq  : forall A1 A2 u1 u2 v1 v2,
               A1 ≃ A2 @ E -> u1 ≃ u2 @ E -> v1 ≃ v2 @ E ->
               Eq A1 u1 v1 ≃ Eq A2 u2 v2 @ E
| EquivRfl : forall t1 t2, t1 ≃ t2 @ E -> refle t1 ≃ refle t2 @ E
| EquivJ   : forall A1 A2 P1 P2 u1 u2 t1 t2 v1 v2 p1 p2,
               A1 ≃ A2 @ E -> P1 ≃ P2 @ E -> u1 ≃ u2 @ E -> t1 ≃ t2 @ E ->
               v1 ≃ v2 @ E -> p1 ≃ p2 @ E ->
               J A1 P1 u1 t1 v1 p1 ≃ J A2 P2 u2 t2 v2 p2 @ E
where "t ≃ u @ E" := (equiv E t u).

Notation "t ~ u" := (t ≃ u @ nil).

(* Inversion of typing for variables *)
Lemma var_inversion :
  forall Γ x A, Γ ⊢ #x : A -> exists B, B ↓ x ⊂ Γ /\ Γ ⊢ A ≡ B.
Proof.
  intros Γ x A h.
  dependent induction h.
  - exists A. split.
    + exact H0.
    + dependent induction Γ.
      * inversion H0. destruct H1. inversion H2.
      * { induction x.
          - inversion H0. destruct H1. inversion H2. subst.
            inversion H. subst. admit. (* Weakening. *)
          - inversion H0. destruct H1. inversion H2. subst.
            admit. (* So annoying, it is obviously true but I need to figure out how. *)
        }
  - destruct IHh1 as (B0 & h3 & h4).
    exists B0. split.
    + exact h3.
    + eapply eTrans.
      * apply eSym. exact H.
      * exact h4.
Admitted.

(* Unicity of typing (for variables at least) *)
Lemma unicity_type_var :
  forall Γ x A B, Γ ⊢ #x : A -> Γ ⊢ #x : B -> Γ ⊢ A ≡ B.
Proof.
  intros Γ x A B h1 h2.
  destruct (var_inversion Γ x A h1) as (A' & h11 & h12).
  destruct (var_inversion Γ x B h2) as (B' & h21 & h22).
  inversion h11 as (A'' & Aeq & Actx).
  inversion h21 as (B'' & Beq & Bctx).
  assert (h : forall y Γ, A'' ↓ y ∈ Γ -> B'' ↓ y ∈ Γ -> A'' = B'').
  { induction y ; intros G hyp1 hyp2.
    - induction G ; inversion hyp1. now inversion hyp2.
    - induction G ; inversion hyp1. inversion hyp2.
      apply (IHy G) ; auto.
  }
  assert (eq : A'' = B'').
  { apply (h x Γ) ; auto. }
  subst.
  eapply eTrans.
  - exact h12.
  - now apply eSym.
Qed.


(* Now let's see how such terms relate. *)
Lemma equiv_equal_gen :
  forall E Γ,
    (forall x y, In (x,y) E -> forall s A1 A2,
                      Γ ⊢ A1 : !s -> Γ ⊢ A2 : !s ->
                      Γ ⊢ #x : A1 -> Γ ⊢ #y : A2 ->
            exists q, Γ ⊢ q : Eq (Σ !s #0) ⟨ A1 , #x ⟩ ⟨ A2 , #y ⟩) ->
    forall t1 t2 T1 T2 s,
      Γ ⊢ T1 : !s -> Γ ⊢ T2 : !s ->
      Γ ⊢ t1 : T1 -> Γ ⊢ t2 : T2 -> t1 ≃ t2 @ E ->
      exists p, Γ ⊢ p : Eq (Σ !s #0) ⟨ T1 , t1 ⟩ ⟨ T2 , t2 ⟩.
Proof.
  intros E Γ h t1 t2 T1 T2 s hT1 hT2 ht1 ht2 sim.
  induction sim.
  - destruct (h x y H s T1 T2 hT1 hT2 ht1 ht2) as (p & hyp).
    exists p. exact hyp.
  - assert (eq : Γ ⊢ T1 ≡ T2).
    { apply (unicity_type_var _ x) ; easy. }
    exists (refle ⟨ T1, # x ⟩). eapply Cnv.
    Focus 2. apply crefle. apply cPair. exact hT1.
    assert (pr : Γ ⊢ #x : (#0) [← T1]).
    { simpl. now rewrite lift0. }
    exact pr.
    + apply eEq.
      * case s. intro n. eapply eRefl.
        { apply cΣ.
          - apply (@cSort _ (U n) (U (S n))).
            + eapply wf_typ. exact ht1.
            + apply Ax0. auto.
          - apply cVar.
            + apply (@wf_cons _ _ (U (S n))).
              apply cSort. eapply wf_typ. exact ht1.
              apply Ax0. auto.
            + exists (! (U n)). split.
              * reflexivity.
              * apply item_hd.
        }
      * eapply eRefl. apply cPair. exact hT1.
        assert (pr : Γ ⊢ #x : (#0) [← T1]).
        { simpl. now rewrite lift0. }
        exact pr.
      * { apply ePair.
          - exact eq.
          - eapply eRefl. exact ht1.
        }
    + induction s. apply cEq.
      * (* { apply cΣ.
          - apply (@cSort _ (U n) (U (S n))).
            + eapply wf_typ. exact ht1.
            + apply Ax0. auto.
          - apply cVar.
            + apply (@wf_cons _ _ (U (S n))).
              apply cSort. eapply wf_typ. exact ht1.
              apply Ax0. auto.
            + exists (! (U n)). split.
              * reflexivity.
              * apply item_hd.
         } *)
        admit. (* Scope problem, wtf... *)
      * { apply cPair.
          - exact hT1.
          - simpl. now rewrite lift0.
        }
      * { apply cPair.
          - exact hT2.
          - simpl. now rewrite lift0.
        }
  - admit. (* we have to build the corresponding terms... *)
  - admit.
Admitted.

Lemma equiv_equal :
  forall Γ t1 t2 T1 T2 s,
    Γ ⊢ T1 : !s -> Γ ⊢ T2 : !s ->
    Γ ⊢ t1 : T1 -> Γ ⊢ t2 : T2 -> t1 ~ t2 ->
    exists p, Γ ⊢ p : Eq (Σ !s #0) ⟨ T1 , t1 ⟩ ⟨ T2 , t2 ⟩.
Proof.
  intros Γ t1 t2 T1 T2 s hT1 hT2 ht1 ht2 sim.
  apply (equiv_equal_gen nil) ; auto.
  intros x y abs. inversion abs.
Defined.

Lemma liftP2: forall M i j k n, i <= n ->
  (M ↑ j # i) ↑ k # (j+n) = (M ↑ k # n) ↑ j # i.
Admitted. (* This comes from Siles work and should hold. *)

Lemma pre_lift_lift0 :
  forall A n k, (A ↑ 1 # 0) ↑ n # (1 + k) = (A ↑ n # k) ↑ 1 # 0.
Proof.
  intros A n k.
  apply liftP2. intuition.
Qed.

Lemma lift_lift0 :
  forall A n k, (A ↑) ↑ n # (S k) = (A ↑ n # k) ↑.
Proof.
  intros A n k.
  apply pre_lift_lift0.
Qed.

Lemma transport_lift :
  forall s A B p n k,
  (transport s A B p) ↑ n # k = transport s (A ↑ n # k) (B ↑ n # k) (p  ↑ n # k).
Proof.
  intros s A B p n k.
  unfold transport. simpl.
  f_equal. f_equal ; apply lift_lift0.
Qed.

Lemma app_lift :
  forall t u n k, (t · u) ↑ n # k = (t ↑ n # k) · (u ↑ n # k).
Proof.
  intros ; simpl ; reflexivity.
Qed.

Lemma equiv_lift :
  forall u v, u ~ v -> forall n k, u ↑ n # k ~ v ↑ n # k.
Proof.
  intros u v h. induction h ; intros n k.
  - inversion H.
  - simpl. destruct (le_gt_dec k x) ; simpl ; apply EquivVar.
  - rewrite app_lift. rewrite transport_lift. now apply EquivTL.
  - rewrite app_lift. rewrite transport_lift. now apply EquivTR.
  - simpl. apply EquivApp.
    + now apply IHh1.
    + now apply IHh2.
  - simpl. apply Equivλ.
    + now apply IHh1.
    + now apply IHh2.
  - simpl. apply EquivΠ.
    + now apply IHh1.
    + now apply IHh2.
  - simpl. apply EquivEq.
    + now apply IHh1.
    + now apply IHh2.
    + now apply IHh3.
  - simpl. apply EquivRfl.
    now apply IHh.
  - simpl. apply EquivJ.
    + now apply IHh1.
    + now apply IHh2.
    + now apply IHh3.
    + now apply IHh4.
    + now apply IHh5.
    + now apply IHh6.
Qed.

Lemma equiv_lift0 :
  forall u v, u ~ v -> forall n, u ↑ n ~ v ↑ n.
Proof.
  intros u v h n.
  now apply equiv_lift.
Qed.

Lemma substP2: forall M N i j n, i <= n ->
  (M ↑ j # i ) [ j+n ← N ] = ( M [ n ← N]) ↑ j # i.
Admitted. (* From Siles. *)

Lemma transport_subst :
  forall s A B p n u,
  (transport s A B p) [n ← u] = transport s (A [n ← u]) (B [n ← u]) (p  [n ← u]).
Proof.
  intros s A B p n u.
  unfold transport. simpl. f_equal. f_equal ;
  apply substP2 ; intuition.
Qed.

Lemma app_subst :
  forall t u n v, (t · u) [n ← v] = (t [n ← v]) · (u [n ← v]).
Proof.
  auto.
Qed.

Lemma equiv_subst :
  forall t1 t2, t1 ~ t2 ->
  forall u1 u2 n,
  u1 ~ u2 -> t1[n ← u1] ~ t2[n ← u2].
Proof.
  intros t1 t2 ht.
  induction ht ; intros iu1 iu2 n hu.
  - inversion H.
  - simpl. destruct (lt_eq_lt_dec x n) ; simpl.
    + destruct s.
      * apply EquivVar.
      * now apply equiv_lift0.
    + apply EquivVar.
  - rewrite app_subst. rewrite transport_subst. apply EquivTL. now apply IHht.
  - rewrite app_subst. rewrite transport_subst. apply EquivTR. now apply IHht.
  - simpl. apply EquivApp.
    + now apply IHht1.
    + now apply IHht2.
  - simpl. apply Equivλ.
    + now apply IHht1.
    + now apply IHht2.
  - simpl. apply EquivΠ.
    + now apply IHht1.
    + now apply IHht2.
  - simpl. apply EquivEq.
    + now apply IHht1.
    + now apply IHht2.
    + now apply IHht3.
  - simpl. apply EquivRfl.
    now apply IHht.
  - simpl. apply EquivJ.
    + now apply IHht1.
    + now apply IHht2.
    + now apply IHht3.
    + now apply IHht4.
    + now apply IHht5.
    + now apply IHht6.
Qed.

(* We now will be defining what it is to be a translation for a context. *)
Inductive ctx_trans_step : Env -> S.Env -> Prop :=
| trans_nil  : ctx_trans_step nil nil
| trans_cons : forall Γ Δ A B, ctx_trans_step Γ Δ -> ι B ~ A -> ctx_trans_step (A :: Γ) (B :: Δ)
.

Definition ctx_trans Γ Δ :=
  ctx_trans_step Γ Δ /\
    Γ ⊣ /\
  S.wf Δ
.

(* And for term typing *)
Definition trans Γ a A Δ b B : Prop :=
  ctx_trans Γ Δ /\
    ι b ~ a /\
    ι B ~ A /\
    Γ ⊢ a : A /\
  S.typ Δ b B
.

(* The next lemma is supposed to say that we can always chose a translation with
   a type having the same head constructor. This has to be divided in several
   lemmata, one for each type of constructor. *)

Delimit Scope Ext_scope with Ext.

Lemma ι_inv_Π :
  forall A B C, Π A B = ι C -> exists A' B', C = S.Π A' B' /\ ι A' = A /\ ι B' = B.
Proof.
  intros A B C h.
  induction C ; simpl in h ; try discriminate.
  exists C1. exists C2. repeat split ; now inversion h.
Qed.

Lemma ι_inv_app :
  forall t u C, t · u = ι C ->
  exists t' u', C = (t' · u')%Ext /\ ι t' = t /\ ι u' = u.
Proof.
  intros t u C h.
  induction C ; simpl in h ; try discriminate.
  exists C1. exists C2. repeat split ; now inversion h.
Qed.

Lemma ι_inv_λ :
  forall A t C, λ A t = ι C ->
  exists A' t', C = S.λ A' t' /\ ι A' = A /\ ι t' = t.
Proof.
  intros A t C h.
  induction C ; simpl in h ; try discriminate.
  exists C1. exists C2. repeat split ; now inversion h.
Qed.

Lemma ι_inv_J :
  forall A P M1 N M2 p C, J A P M1 N M2 p = ι C ->
  exists A' P' M1' N' M2' p', C = S.J A' P' M1' N' M2' p' /\
                         ι A' = A /\ ι P' = P /\ ι M1' = M1 /\
                         ι N' = N /\ ι M2' = M2 /\ ι p' = p.
Proof.
  intros A P M1 N M2 p C h.
  induction C ; simpl in h ; try discriminate.
  exists C1, C2, C3, C4, C5, C6. inversion h. now repeat split.
Qed.

Lemma ι_inv_sort :
  forall s C, !s = ι C -> C = (!s)%Ext.
Proof.
  intros s C h.
  induction C ; simpl in h ; try discriminate.
  now inversion h.
Qed.

Lemma ι_inv_var :
  forall n C, #n = ι C -> C = (#n)%Ext.
Proof.
  intros n C h.
  induction C ; simpl in h ; try discriminate.
  now inversion h.
Qed.

Lemma ι_inv_lift :
  forall A C n m, A ↑ n # m = ι C ->
  exists A', C = (A' ↑ n # m)%Ext /\ ι A' = A.
Proof.
  intro A ; induction A ;
  intro C ; induction C ;
  intros  n m h ;
  simpl in h ; try discriminate ;
  try (destruct (le_gt_dec m v) ; discriminate).
  - exists (#v)%Ext. simpl. destruct (le_gt_dec m v) ;
    inversion h ; split ; simpl ; easy.
  - inversion h ; subst. exists (!s0)%Ext. split ; easy.
  - inversion h.
    destruct (IHA1 _ _ _ H0) as (A1' & h11 & h12).
    destruct (IHA2 _ _ _ H1) as (A2' & h21 & h22).
    subst.
    exists (S.Π A1' A2'). split ; simpl ; easy.
  - inversion h.
    destruct (IHA1 _ _ _ H0) as (A1' & h11 & h12).
    destruct (IHA2 _ _ _ H1) as (A2' & h21 & h22).
    subst. exists (S.λ A1' A2'). split ; simpl ; easy.
  - inversion h.
    destruct (IHA1 _ _ _ H0) as (A1' & h11 & h12).
    destruct (IHA2 _ _ _ H1) as (A2' & h21 & h22).
    subst. exists (A1' · A2')%Ext. split ; simpl ; easy.
  - inversion h.
    destruct (IHA1 _ _ _ H0) as (A1' & h11 & h12).
    destruct (IHA2 _ _ _ H1) as (A2' & h21 & h22).
    destruct (IHA3 _ _ _ H2) as (A3' & h31 & h32).
    subst. exists (S.Eq A1' A2' A3')%Ext. split ; simpl ; easy.
  - inversion h.
    destruct (IHA _ _ _ H0) as (A' & h1 & h2).
    subst. exists (S.refle A'). split ; simpl ; easy.
  - inversion h.
    destruct (IHA1 _ _ _ H0) as (A1' & h11 & h12).
    destruct (IHA2 _ _ _ H1) as (A2' & h21 & h22).
    destruct (IHA3 _ _ _ H2) as (A3' & h31 & h32).
    destruct (IHA4 _ _ _ H3) as (A4' & h41 & h42).
    destruct (IHA5 _ _ _ H4) as (A5' & h51 & h52).
    destruct (IHA6 _ _ _ H5) as (A6' & h61 & h62).
    subst. exists (S.J A1' A2' A3' A4' A5' A6'). split ; simpl ; easy.
  - inversion h.
    destruct (IHA1 _ _ _ H0) as (A1' & h11 & h12).
    destruct (IHA2 _ _ _ H1) as (A2' & h21 & h22).
    subst. exists (S.Σ A1' A2'). split ; simpl ; easy.
  - inversion h.
    destruct (IHA1 _ _ _ H0) as (A1' & h11 & h12).
    destruct (IHA2 _ _ _ H1) as (A2' & h21 & h22).
    subst. exists (S.Pair A1' A2'). split ; simpl ; easy.
  - inversion h.
    destruct (IHA _ _ _ H0) as (A' & h1 & h2).
    subst. exists (S.π1 A'). split ; simpl ; easy.
  - inversion h.
    destruct (IHA _ _ _ H0) as (A' & h1 & h2).
    subst. exists (S.π2 A'). split ; simpl ; easy.
Qed.

Lemma ι_inv_lift0 :
  forall A C, A ↑ = ι C ->
  exists A', C = (A' ↑)%Ext /\ ι A' = A.
Proof.
  intros A C h.
  now apply ι_inv_lift.
Qed.

Lemma ι_inj : forall a b, ι a = ι b -> a = b.
Proof.
  intro a ; induction a ; intro b ; induction b ; intro h ;
  simpl in h ; try discriminate ; inversion h ; try easy ;
  f_equal ; auto.
Qed.

Lemma ι_inv_transport :
  forall s A B p t C, (transport s A B p) · t = ι C ->
  exists (A' B' p' t' : S.Term),
    C = ((S.λ A' (S.J !s #0 (A' ↑) #0 (B' ↑) (p' ↑))) · t')%Ext /\
       ι A' = A /\ ι B' = B /\ ι p' = p /\ ι t' = t.
Proof.
  intros s A B p t C h.
  unfold transport in h.
  destruct (ι_inv_app _ _ _ h) as (C1 & C2 & h1 & h2' & h3).
  assert (h2 : λ A (J !s #0 (A ↑) #0 (B ↑) (p ↑)) = ι C1) by easy. clear h2'.
  destruct (ι_inv_λ _ _ _ h2) as (C11 & C12 & h21 & h22 & h23').
  assert (h23 : J !s #0 (A ↑) #0 (B ↑) (p ↑) = ι C12) by easy. clear h23'.
  destruct (ι_inv_J _ _ _ _ _ _ _ h23)
    as (
      C121 & C122 & C123 & C124 & C125 & C126 &
      h231 & h232' & h233' & h234' & h235' & h236' & h237'
    ).
  assert (h232 : !s = ι C121) by easy ; clear h232'.
  assert (h233 : #0 = ι C122) by easy ; clear h233'.
  assert (h235 : #0 = ι C124) by easy ; clear h235'.
  assert (h234 : A ↑ = ι C123) by easy ; clear h234'.
  assert (h236 : B ↑ = ι C125) by easy ; clear h236'.
  assert (h237 : p ↑ = ι C126) by easy ; clear h237'.
  pose proof (ι_inv_sort _ _ h232) as h121.
  pose proof (ι_inv_var _ _ h233) as h122.
  pose proof (ι_inv_var _ _ h235) as h124.
  destruct (ι_inv_lift0 _ _ h234) as (A' & h123 & h123').
  destruct (ι_inv_lift0 _ _ h236) as (B' & h125 & h125').
  destruct (ι_inv_lift0 _ _ h237) as (p' & h126 & h126').
  subst.
  exists C11, B', p', C2. repeat split ; simpl ; try easy.
  now destruct (ι_inj _ _ h123').
Qed.

Lemma ι_lift : forall A n m, ι (A ↑ n # m)%Ext = (ι A) ↑ n # m.
Proof.
  intro A. induction A ; intros n m ;
  try (simpl ; f_equal ; easy).
  simpl. destruct (le_gt_dec m v) ; now simpl.
Qed.

Lemma ι_lift0 : forall A, ι (A ↑)%Ext = (ι A) ↑.
Proof.
  intro A. apply ι_lift.
Qed.

Definition next (s : Sorts) : Sorts.
  destruct s. exact (U (n+1)).
Defined.

Lemma SortSort : forall s, Ax s (next s).
Proof.
  intro s. destruct s. simpl. apply Ax0. Omega.omega.
Defined.

Lemma destruct_eq :
  forall {Γ s p T1 T2 t1 t2},
    Γ ⊢ p : Eq (Σ !s #0) ⟨ T1 , t1 ⟩ ⟨ T2 , t2 ⟩ ->
    exists p1, Γ ⊢ p1 : Eq !s T1 T2 /\
    exists p2, Γ ⊢ p2 : Eq T2 ((transport s T1 T2 p1) · t1) t2.
Proof.
  intros Γ s p T1 T2 t1 t2 h.
  exists (J (Σ !s #0) (Eq !s (T1 ↑) (π1 #0)) ⟨ T1 , t1 ⟩ (refle T1) ⟨ T2 , t2 ⟩ p).
  split.
  - eapply (@Cnv _ _ _ _ s).
    Focus 2.
      eapply cJ with (s := next s).
      + eapply cEq with (s := next s).
        * { eapply cSort.
            - eapply wf_cons with (s := next s).
              destruct s. simpl. (* eapply cΣ. *)
              (* + eapply cSort. *)
              (*   * eapply wf_typ. exact h. *)
              (*   * destruct (SortSort s). destruct x. exact H. *)

    (* The following is only true up to β-equality. *)
    (* assert (eq : (Eq !s (T1 ↑) (π1 #0)) [← ⟨ T2 , t2 ⟩] = Eq !s T1 T2) by admit. *)
    admit.
  - admit.
Admitted.

Lemma typeq :
  forall Γ t s A B p,
    Γ ⊢ p : Eq (Σ !t #0) ⟨ !s , A ⟩ ⟨ !s , B ⟩ ->
    exists q, Γ ⊢ q : Eq !s A B.
Proof.
  intros Γ t s A B p h.
  destruct (destruct_eq h) as (p1 & h1 & p2 & h2).
  admit.
Admitted.

(* We'll also need to be able to inverse path for ι... *)

Lemma trans_Π :
  forall Γ a A1 A2 Δ b B, trans Γ a (Π A1 A2) Δ b B ->
  exists B1 B2 c, trans Γ a (Π A1 A2) Δ c (S.Π B1 B2).
Proof.
  intros Γ a A1 A2 Δ b B h.
  destruct h as (h1 & h2 & h3 & h4 & h5).
  revert h2 h5. revert b.

  dependent induction h3 ; intros b h2 h5.
  - destruct (ι_inv_transport _ _ _ _ _ _ x) as (
      A' & B' & p' & t' & eq1 & eq2 & eq3 & eq4 & eq5
    ).
    assert (eq5' : t1 = ι t') by intuition.
    pose proof (IHh3 A1 A2 t' h1 eq5' eq_refl h4).
    assert (path : exists p, (Δ ⊢ p : S.Eq !s B t')%Ext).
    + admit.
      (* We have to build an equality between B and t1 to transport b along it
         and use this one as argument to H... *)
    + (* Here we want to use "transport s B t' q" on b. *)
      destruct path as (q & hq).
      (* pose proof (H (S.J !s #0 B b t' q)%Ext). *)
      pose proof (H ((S.λ B (S.J !s #0 (B ↑) #0 (t' ↑) (q ↑))) · b)%Ext).
      apply H0.
      * simpl. rewrite !ι_lift0.
        apply EquivTL. exact h2.
      * admit.
  - destruct (ι_inv_Π A0 B1 B x) as (B0 & B2 & eq1 & eq2 & eq3).
    exists B0. exists B2.
    exists b.
    split ; try exact h1 ; repeat split.
    + exact h2.
    + simpl. apply EquivΠ.
      * now rewrite eq2.
      * now rewrite eq3.
    + exact h4.
    + now rewrite <- eq1.
Admitted.


Lemma trans_Eq :
  forall Γ a A u1 u2 Δ b B, trans Γ a (Eq A u1 u2) Δ b B ->
  exists B v1 v2 c, trans Γ a (Eq A u1 u2) Δ c (S.Eq B v1 v2).
Proof.
Admitted.

Lemma trans_Σ :
  forall Γ a A1 A2 Δ b B, trans Γ a (Σ A1 A2) Δ b B ->
  exists B1 B2 c, trans Γ a (Σ A1 A2) Δ c (S.Σ B1 B2).
Proof.
Admitted.

Theorem validity :
  (forall Δ, (Δ ⊣)%Ext -> exists Γ, ctx_trans Γ Δ) /\
  (forall Δ b B,
      (Δ ⊢ b : B)%Ext ->
      (exists Γ, ctx_trans Γ Δ) /\
      (forall Γ, ctx_trans Γ Δ -> exists a A, trans Γ a A Δ b B)) /\
  (forall Δ b1 b2,
      (Δ ⊢ b1 ≡ b2)%Ext ->
      (exists Γ, ctx_trans Γ Δ) /\
      (forall Γ, ctx_trans Γ Δ ->
         exists p q A1 A2 a1 a2 B1 B2 s,
           trans Γ p (Eq (Σ !s #0) ⟨ A1 , a1 ⟩ ⟨ A2 , a2 ⟩)
                 Δ q (S.Eq (S.Σ !s #0) ⟨ B1 , b1 ⟩ ⟨ B2 , b2 ⟩)%Ext)).
Proof.
Admitted.
