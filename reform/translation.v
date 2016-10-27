Require Import List.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt Le Gt.

Require Sorts PTS PTS_Ext.
Module S := PTS_Ext.
Module T := PTS.
Import T Sorts Sorts.withoutProp.

(* We first would like to express an equivalence between terms that can either
   be in S or in T. If we only look at the terms, then S is included in T. *)
Fixpoint ι (t : S.Term) : Term :=
  match t with
  | S.Var x => #x
  | S.Sort s => !s
  | S.Π A B => Π (ι A) (ι B)
  | S.λ A t => λ (ι A) (ι t)
  | S.App t u => (ι t) · (ι u)
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
  induction h.
  (* It would be nice to be able to do an induction that doesn't come up with
     another x... There are only two possible cases, how do we tell it to coq? *)
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
Inductive ctx_trans : Env -> S.Env -> Prop :=
| trans_nil  : ctx_trans nil nil
| trans_cons : forall Γ Δ A B, ctx_trans Γ Δ -> ι B ~ A -> ctx_trans (A :: Γ) (B :: Δ)
.

(* And for term typing *)
Definition trans Γ a A Δ b B : Prop :=
  ctx_trans Γ Δ /\
    ι b ~ a /\
    ι B ~ A.

(* The next lemma is supposed to say that we can always chose a translation with a type
   having the same head constructor. This has to be divided in several lemmata, one for each
   type of constructor. *)

Require Import Coq.Program.Equality.

Lemma ι_inv_Π :
  forall A B C, Π A B = ι C -> exists A' B', C = S.Π A' B' /\ ι A' = A /\ ι B' = B.
Proof.
  intros A B C h.
  induction C ; simpl in h ; try discriminate.
  exists C1. exists C2. repeat split ; now inversion h.
Qed.

Lemma trans_Π :
  forall Γ a A1 A2 Δ b B, trans Γ a (Π A1 A2) Δ b B ->
  exists B1 B2 c, trans Γ a (Π A1 A2) Δ c (S.Π B1 B2).
Proof.
  intros Γ a A1 A2 Δ b B h.
  destruct h as (h1 & h2 & h3).

  dependent induction h3.
  - admit.
  - destruct (ι_inv_Π A0 B1 B x) as (B0 & B2 & eq1 & eq2 & eq3).
    exists B0. exists B2.
    exists b. (* We have to change the b. Indeed we forgot to ask for typing. *)
    repeat split.
    + exact h1.
    + exact h2. (* This will have to change. *)
    + simpl. apply EquivΠ.
      * now rewrite eq2.
      * now rewrite eq3.
Admitted.






