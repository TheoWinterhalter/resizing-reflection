Set Printing Universes.
Set Universe Polymorphism.

Add LoadPath "../quotient".
Require Import Base.
Require Import RRnType.


Definition quotient (A : Type) (R : A -> A -> hProp)
: Type := { P : A -> hProp | RR1 (trunc minus1 (isEqClass R P)) (ishType_trunc _ _) }.

Notation "A // R" := (quotient A R) (at level 90).

(* Let's try it with Z/2Z *)

Require Import ZArith.

(* Definition Z@{i} := Z : let _ := Set : Type@{i} in Type@{i}. *)

Inductive R2Ztype : Z -> Z -> Type :=
| diff_even : forall n m k : Z, heq (m - n)%Z (2 * k)%Z -> R2Ztype n m.

(* Require Eqdep_dec. *)

Require Import MyEqDepDec.

(* I'll allow myself anything, we will hide it with Qed *)
Lemma division_unicity : forall n k l, heq n (2 * k)%Z -> heq n (2 * l)%Z -> heq k l.
Proof.
  intros n k l h1 h2.
  inversion h1 as [hh1].
  inversion h2 as [hh2].
  cut (eq k l).
  - intro h.
    now destruct h.
  - omega.
Qed.

Lemma division_unicity2 : forall n k l, heq n (2 * k + 1)%Z -> heq n (2 * l + 1)%Z -> heq k l.
Proof.
  intros n k l h1 h2.
  inversion h1 as [hh1].
  inversion h2 as [hh2].
  cut (eq k l).
  - intro h.
    now destruct h.
  - omega.
Qed.

(* To replace Z.eq_dec *)
Lemma Pos_eq_dec : forall p q : positive, hsum (heq p q) ((heq p q) -> False).
Proof.
  intro p.
  induction p ; destruct q ; try (now apply inl) ; try (now apply inr).
  - destruct (IHp q).
    + left.
      now destruct a.
    + right.
      intro absurd.
      apply b.
      now inversion absurd.
  - destruct (IHp q).
    + left ; now destruct a.
    + right ; intro absurd ; apply b ; now inversion absurd.
Qed.

Lemma Zeq_dec : forall x y : Z, hsum (heq x y) ((heq x y) -> False).
Proof.
  intro x.
  induction x ; destruct y ; try (now apply inl) ; try (now apply inr).
  - destruct (Pos_eq_dec p p0).
    + left ; now destruct a.
    + right ; intro absurd ; apply b ; now inversion absurd.
  - destruct (Pos_eq_dec p p0).
    + left ; now destruct a.
    + right ; intro absurd ; apply b ; now inversion absurd.
Qed.

Lemma R2ZhProp : forall n m : Z, ishType minus1 (R2Ztype n m).
Proof.
  intros n m.
  apply hsuc.
  intros x y.
  apply hctr.
  destruct x as [n m k e].
  destruct y as [n m l f].
  assert (heq k l) as k_l.
  {
    eapply (division_unicity).
    - exact e.
    - exact f.
  }
  destruct k_l.
  assert (heq e f) as e_f.
  - apply eq_proofs_unicity.
    intros x y.
    destruct (Zeq_dec x y).
    + now left.
    + now right.
  - destruct e_f.
    exists (heq_refl (diff_even n m k e)).
    intro p.
    apply eq_proofs_unicity.
    intros x y.
    destruct x as [n m k' e'].
    destruct y as [n m l f].
    assert (heq l k') as l_k'.
    {
      now apply (division_unicity (m - n)%Z).
    }
    destruct l_k'.
    assert (heq f e') as f_e'.
    + apply eq_proofs_unicity.
      intros x y.
      destruct (Zeq_dec x y).
      * now left.
      * now right.
    + destruct f_e'.
      now apply inl.
Defined.

Definition R2Z (n m : Z) : hProp := exist _ (RR1 (R2Ztype n m) (R2ZhProp n m)) (RR1_hProp _ (R2ZhProp n m)).

Definition Z2 := Z // R2Z.

Inductive even : Z -> Type :=
  is_even : forall n k : Z, heq n (2 * k)%Z -> even n.

Lemma evenhProp : forall z, ishProp (even z).
Proof.
  intro z.
  apply hsuc.
  intros x y.
  apply hctr.
  destruct x.
  destruct y.
  cut (heq k k0).
  - intro hh.
    destruct hh.
    assert (heq h h0).
    + apply eq_proofs_unicity.
      intros x y.
      destruct (Zeq_dec x y).
      * destruct a.
        now apply inl.
      * apply inr.
        intro eqxy.
        destruct eqxy.
        now apply b.
    + destruct X.
      exists (heq_refl (is_even n k h)).
      intro p.
      apply eq_proofs_unicity.
      intros x y.
      destruct x ; destruct y.
      assert (heq k0 k1).
      {
        now apply (division_unicity n).
      }
      destruct X.
      assert (heq h0 h1).
      {
        apply eq_proofs_unicity.
        intros x y.
        destruct (Zeq_dec x y).
        - destruct a ; now left.
        - right ; intro eqxy ; destruct eqxy ; now apply b.
      }
      destruct X.
      now apply inl.
  - now apply (division_unicity n).
Defined.

(* m - 0 = m *)
Lemma minus0_id : forall n, heq (n - 0)%Z n.
Proof.
  induction n ; easy.
Defined.

Unset Printing Universes.

Lemma conveq : forall n k, heq (n - 0)%Z (2 * k)%Z -> heq n (2 * k)%Z.
Proof.
  intros n k h.
  apply (heq_trans _ (n - 0)%Z).
  - apply heq_sym.
    apply minus0_id.
  - exact h.
Defined.

Definition g (y : Z) (p : RR1 (R2Ztype 0 y) (R2ZhProp 0 y)) :=
  match (RR1_unbox p) in (R2Ztype 0%Z z) return (even z) with
  | diff_even 0%Z n k h => is_even n k (conveq n k h)
  end.

Definition h (y : Z) (p : even y) :=
  match p in (even z) return (RR1 (R2Ztype 0 z) (R2ZhProp 0 z)) with
    | is_even n k h =>
      RR1_box (diff_even 0%Z n k (heq_trans (n-0)%Z n (2*k)%Z (minus0_id n) h))
  end.

Lemma hg_id0 :
  forall n k hh,
    heq (h n (g n (RR1_box(diff_even 0%Z n k hh))))
        (RR1_box (diff_even 0%Z n k hh)).
Proof.
  intros n k hh.
  unfold g.
  rewrite RR1_unbox_box.
  unfold h.
  apply hf_equal.
  apply hf_equal.
  apply eq_proofs_unicity.
  apply Zeq_dec.
Defined.

Definition hg_id1 (y : Z) (a : RR1 (R2Ztype 0%Z y) (R2ZhProp 0 y)) :=
  match (RR1_unbox a) as p in (R2Ztype 0%Z z) return
        (@heq (RR1 (R2Ztype 0 z) (R2ZhProp 0 z))
              (h z (g z (RR1_box p))) (RR1_box p))
  with
  | diff_even 0%Z n k hh => hg_id0 n k hh
  end.

Lemma hg_id : forall y a, heq (h y (g y a)) a.
Proof.
  intros y a.
  pose proof (hg_id1 y a) as h.
  now rewrite !RR1_box_unbox in h.
Defined.

Lemma gh_id0 :
  forall n k hh, heq (g n (h n (is_even n k hh))) (is_even n k hh).
Proof.
  intros n k hh.
  unfold h.
  unfold g.
  rewrite RR1_unbox_box.
  apply hf_equal.
  apply eq_proofs_unicity.
  apply Zeq_dec.
Defined.

Definition gh_id y a : heq (g y (h y a)) a :=
  match a as p in (even z) return (@heq (even z) (g z (h z p)) p) with
  | is_even n k hh => gh_id0 n k hh
  end.

Let evenClass : Z2.
Proof.
  exists (fun z => exist _ (even z) (evenhProp z)).
  apply RR1_box. apply tr.
  exists 0%Z. intro y.
  exists (g y). split.
  - exists (h y). unfold comp, id, homo. apply hg_id.
  - exists (h y). unfold comp, id, homo. apply gh_id.
Defined.

Let fooP (foon : Z2) (z : Z) : hProp.
  simple refine (forall x : Z2, heq x foon -> let (P, _) := x in pi1 (P z) ; _).
  apply forall_hProp. intro x.
  apply forall_hProp. intro h. destruct x as [px hx].
  now destruct (px z).
Defined.

(* Ltac rrintro x := *)
(*   match goal with *)
(*     | |- RR1 (forall y : ?A, ?B) ?h => (apply RR1_box ; intro x) *)
(*     (* | |- RR1 (?A -> ?B) ?h => (apply RR1_box ; intro x) *) *)
(*     | |- forall y : ?A, ?B => (intro x) *)
(*     (* | |- ?A -> ?B => (intro x) *) *)
(*     | _ => fail *)
(*   end. *)

(* Ltac rrintro x := *)
(*   match goal with *)
(*     | |- RR1 ?A ?h => (apply RR1_box ; intro x) *)
(*     | _ => intro x *)
(*   end. *)

(* Ltac rrintro x := ((try apply RR1_box) ; intro x). *)

Tactic Notation "rrintro" ident(x) :=
  (try apply RR1_box) ; intro x.

(* Ltac rrintros2 x y := rrintro x ; rrintro y. *)
(* Ltac rrintros3 x y z := rrintro x ; rrintro y ; rrintro z. *)
(* Ltac rrintros4 x y z t := rrintro x ; rrintro y ; rrintro z ; rrintro t. *)

Tactic Notation "rrintros" ident(x) := rrintro x.
Tactic Notation "rrintros" ident(x) ident(y) := rrintro x ; rrintro y.
Tactic Notation "rrintros" ident(x) ident(y) ident(z) :=
  rrintro x ; rrintro y ; rrintro z.
Tactic Notation "rrintros" ident(x) ident(y) ident(z) ident(t) :=
  rrintro x ; rrintro y ; rrintro z ; rrintro t.

Fixpoint foo (n : nat) : Z2.
  destruct n.
  - exact evenClass.
  - simple refine (exist _ (fun z => _) _).
    + simple refine ((RR1 (pi1 (fooP (foo n) z)) _) ; _).
      * destruct (fooP (foo n) z) as [T hT]. exact hT.
      * apply RR1_hProp.
    + destruct (foo n) as [P hP]. pose proof (RR1_unbox hP) as uhP.
      apply RR1_box.
      simple refine (trunc_ind (fun aa => _) _ uhP).
      * intro aa. apply ishType_trunc.
      * intro a. destruct a as [z h].
        apply tr. exists z. intro y. pose proof (h y) as hy. destruct hy as [f hf].
        { simple refine (exist _ (fun rzy => _) _).
          - simpl. rrintros x eq.
            rewrite eq. now apply f.
          - destruct hf as [[g1 hg1] [g2 hg2]]. split.
            + simple refine (exist _ (fun u => _) _).
              * simpl in u. simpl. apply g1.
                pose proof (RR1_unbox u) as uu. now apply (uu (P ; hP)).
              * unfold homo. intro a. unfold comp. unfold id.
                rewrite RR1_unbox_box. apply hg1.
            + simple refine (exist _ (fun u => _) _).
              
              * apply g2. now apply (RR1_unbox u (P ; hP)).
              * unfold homo. intro a. unfold comp. unfold id.
                unfold comp in hg2.
                simpl in a.
                rewrite <- RR1_box_unbox. apply hf_equal.
                apply dep_fun_ext. intro x.
                apply dep_fun_ext. intro eqx.
                unfold internal_heq_rew_r.
                rewrite hg2. unfold id.
                now destruct eqx.
        }
Defined.

(* END *)
