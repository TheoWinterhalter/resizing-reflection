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
(*Unset Printing Notations.
Print Z2.
Set Printing Notations.*)

(* Even though Z fits in Set, it is not the case of Z/2Z which should be smaller (bool : Set!) *)
Fail Check Z2 : Set.

Inductive even : Z -> Type :=
  is_even : forall n k : Z, heq n (2 * k)%Z -> even n.

Inductive odd : Z -> Type :=
  is_odd : forall n k : Z, heq n (2 * k + 1)%Z -> odd n.

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

Lemma oddhProp : forall z, ishProp (odd z).
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
      exists (heq_refl (is_odd n k h)).
      intro p.
      apply eq_proofs_unicity.
      intros x y.
      destruct x ; destruct y.
      assert (heq k0 k1).
      {
        now apply (division_unicity2 n).
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
  - now apply (division_unicity2 n).
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

Definition g (y : Z) (p : R2Ztype 0%Z y) :=
  match p in (R2Ztype 0%Z z) return (even z) with
  | diff_even 0%Z n k h => is_even n k (conveq n k h)
  end.

Definition h (y : Z) (p : even y) :=
  match p in (even z) return (R2Ztype 0%Z z) with
  | is_even n k h => diff_even 0%Z n k (heq_trans (n-0)%Z n (2*k)%Z (minus0_id n) h)
  end.

Lemma hf_equal : forall {A B : Type} (f : A -> B) {x y : A}, heq x y -> heq (f x) (f y).
Proof.
  intros A B f x y h.
  now destruct h.
Defined.

Lemma hg_id0 : forall n k hh, heq (h n (g n (diff_even 0%Z n k hh))) (diff_even 0%Z n k hh).
Proof.
  intros n k hh.
  unfold g.
  unfold h.
  apply hf_equal.
  apply eq_proofs_unicity.
  apply Zeq_dec.
Defined.

Definition hg_id y a : heq (h y (g y a)) a :=
  match a as p in (R2Ztype 0%Z z) return (@heq (R2Ztype 0%Z z) (h z (g z p)) p) with
  | diff_even 0%Z n k hh => hg_id0 n k hh
  end.

Lemma gh_id0 : forall n k hh, heq (g n (h n (is_even n k hh))) (is_even n k hh).
Proof.
  intros n k hh.
  unfold h.
  unfold g.
  apply hf_equal.
  apply eq_proofs_unicity.
  apply Zeq_dec.
Defined.

Definition gh_id y a : heq (g y (h y a)) a :=
  match a as p in (even z) return (@heq (even z) (g z (h z p)) p) with
  | is_even n k hh => gh_id0 n k hh
  end.

(* Let's do it again but for odds *)

(* Let's use omega here too *)
Lemma g2_proof : forall n k, heq (n - 1)%Z (2 * k)%Z -> heq n (2 * k + 1)%Z.
Proof.
  intros n k hh.
  cut (eq n (2 * k + 1))%Z.
  - intro hhh ; now destruct hhh.
  - assert (eq (n - 1) (2 * k))%Z.
    + now inversion hh.
    + omega.
Qed.

Definition g2 (y : Z) (p : R2Ztype 1%Z y) :=
  match p in (R2Ztype 1%Z z) return (odd z) with
  | diff_even 1%Z n k hh => is_odd n k (g2_proof n k hh)
  end.

Lemma h2_proof : forall n k, heq n (2 * k + 1)%Z -> heq (n - 1)%Z (2 * k)%Z.
Proof.
  intros n k hh.
  assert (eq (n - 1)%Z (2*k))%Z.
  - inversion hh.
    omega.
  - now destruct H.
Qed.

Definition h2 (y : Z) (p : odd y) :=
  match p in (odd z) return (R2Ztype 1%Z z) with
  | is_odd n k hh => diff_even 1%Z n k (h2_proof n k hh)
  end.

Lemma h2g2_id0 : forall n k hh, heq (h2 n (g2 n (diff_even 1%Z n k hh))) (diff_even 1%Z n k hh).
Proof.
  intros n k hh.
  unfold g2.
  unfold h2.
  apply hf_equal.
  apply eq_proofs_unicity.
  apply Zeq_dec.
Defined.

Definition h2g2_id y a : heq (h2 y (g2 y a)) a :=
  match a as p in (R2Ztype 1%Z z) return (@heq (R2Ztype 1%Z z) (h2 z (g2 z p)) p) with
  | diff_even 1%Z n k hh => h2g2_id0 n k hh
  end.

Lemma g2h2_id0 : forall n k hh, heq (g2 n (h2 n (is_odd n k hh))) (is_odd n k hh).
Proof.
  intros n k hh.
  unfold h2.
  unfold g2.
  apply hf_equal.
  apply eq_proofs_unicity.
  apply Zeq_dec.
Defined.

Definition g2h2_id y a : heq (g2 y (h2 y a)) a :=
  match a as p in (odd z) return (@heq (odd z) (g2 z (h2 z p)) p) with
  | is_odd n k hh => g2h2_id0 n k hh
  end.

Let f (x : bool) : Z2.
Proof.
  destruct x.
  - exists (fun z => exist _ (even z) (evenhProp z)).
    (*compute.*) (* This line causes a loop! *)
    (* We need something to work on RR1 trunc instead of trunc *)
    apply RR1_box.
    apply tr.
    exists 0%Z.
    intro y.
    exists (fun x => g y (RR1_unbox x)).
    split.
    + exists (fun x => RR1_box (h y x)).
  (*     apply hg_id. *)
  (*   + exists (h y). *)
  (*     apply gh_id. *)
  (* - exists (fun z => exist _ (odd z) (oddhProp z)). *)
  (*   compute. *)
  (*   apply (RR1_lift tr). *)
  (*   exists 1%Z. *)
  (*   intro y. *)
  (*   exists (g2 y) ; split. *)
  (*   + exists (h2 y) ; apply h2g2_id. *)
  (*   + exists (h2 y) ; apply g2h2_id. *)
(* Defined. *)
Admitted.        

Axiom ff : forall X, X.

Definition pi2 (T : hProp) : ishProp (pi1 T) :=
  let (_, h) := T in h.

Let fooP (foon : Z2) (z : Z) : hProp.
  simple refine (forall x : Z2, heq x foon -> let (P, _) := x in pi1 (P z) ; _).
  apply forall_hProp. intro x.
  apply forall_hProp. intro h. destruct x as [px hx].
  now destruct (px z).
Defined.

(* Better later than never: R2Z is an equivalence. *)
Lemma isEqRelR2Z : isEqRel R2Z.
Proof.
  split.
  - intro z. simpl. apply RR1_box.
    exists 0%Z. simpl. now rewrite Z.sub_diag.
  - simpl. intros x y h. apply RR1_box.
    pose proof (RR1_unbox h) as hh. destruct hh as [n m k p].
    exists (-k)%Z. assert (eq (n - m)%Z (- (m - n))%Z) by omega.
    assert (eq (m - n)%Z (2 * k)%Z).
    + now inversion p.
    + assert (eq (n - m)%Z (2 * - k)%Z) by omega.
      now destruct H1.
  - intros x y z hyz hxy. simpl in *. apply RR1_box.
    pose proof (RR1_unbox hyz) as ryz. destruct ryz as [n m k p].
    pose proof (RR1_unbox hxy) as rxy. destruct rxy as [x n l q].
    exists (k + l)%Z. assert (eq (m - x)%Z (2 * (k + l))%Z).
    + assert (eq (m - n)%Z (2 * k)%Z) by (now inversion p).
      assert (eq (n - x)%Z (2 * l)%Z) by (now inversion q).
      omega.
    + now destruct H.
Qed. (* It uses omega and ugly stuff... *)

Definition bar (foo : nat -> Z2) (n : nat) (z : Z) :
  RR1 (pi1 (fooP (foo n) z)) (let h0 := fooP (foo n) z in pi2 h0) -> pi1 (R2Z 0%Z z).
  intro h. simpl.
  apply RR1_box.
  pose proof (RR1_unbox h) as uh. simpl in uh.
Abort.

(* Set Printing Universes. *)
(* Unset Printing Notations. *)
Fixpoint foo (n : nat) : Z2.
  destruct n.
  - exact (f false).
  - simple refine (exist _ (fun z => _) _).
    + simple refine ((RR1 (pi1 (fooP (foo n) z)) _) ; _).
      * destruct (fooP (foo n) z) as [T hT]. exact hT.
      * apply RR1_hProp.
    + (* use foo directly somehow? *)
      destruct (foo n) as [P hP]. pose proof (RR1_unbox hP) as uhP.
      apply RR1_box.
      simple refine (trunc_ind (fun aa => _) _ uhP).
      * intro aa. apply ishType_trunc.
      * intro a. destruct a as [z h].
        apply tr. exists z. intro y. pose proof (h y) as hy. destruct hy as [f hf].
        { simple refine (exist _ (fun rzy => _) _).
          - simpl. apply RR1_box. intros x eq. pose proof (heq_sym _ _ eq) as seq. destruct seq. simpl.
            now apply f.
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
                
                
                destruct (heq_sym x (P ; hP) eqx).
                rewrite hg2. unfold id.
                apply hf_equal.

                apply eq_proofs_unicity. intros u v.
                

                apply ff.
        }       
Defined.

(* END *)
