Set Printing Universes.
Set Universe Polymorphism.

Add LoadPath "../quotient".
Require Import Base.
Require Import NType.

Definition quotient A (R : A -> A -> hProp) := { P : A -> hProp | (trunc minus1 (isEqClass R P)) }.
(* Definition quotient@{i j k l m n r e3 e10 e11 e12 e13 e14 e15 e16 truc} (A : Type@{i}) (R : A -> A -> hProp@{j k l}) : Type@{i} *)
(*   := { P : A -> hProp@{m n r} | (trunc@{i} minus1 (isEqClass@{i i e3 j k l m n r e10 e11 e12 e13 e14 e15 e16} R P)) }. *)
Notation "A // R" := (quotient A R) (at level 90).

(* Section Foo. *)

(*   Universes i j k l. *)
(*   (*)Let X := Type@{i} : Type@{j}.*) *)
(*   Let Y := Type@{j} : Type@{k}. *)
(*   Parameter T : Type@{j}. *)
(*   Parameter R : T -> T -> hProp@{l j l}. *)

(*   Parameter P : T -> hProp@{l j l}. *)
(*   Parameter eqP : isEqClass R P. *)

(*   (* Definition foo : T // R := exist _ P (tr eqP). *) *)

(*   (* Goal T // R. *) *)
(*   (* unfold quotient. *) *)
(*   (* exists P. apply tr. exact eqP. *) *)
(*   (* Defined. *) *)

(*   Check T // R : Type@{j}. *)

(* End Foo. *)

(* Let's try it with Z/2Z *)

Require Import ZArith.

(* Definition Z@{i} := Z : let _ := Set : Type@{i} in Type@{i}. *)

Inductive R2Ztype : Z -> Z -> Type :=
| diff_even : forall n m k : Z, heq (m - n)%Z (2 * k)%Z -> R2Ztype n m.

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

Definition R2Z (n m : Z) : hProp := exist _ (R2Ztype n m) (R2ZhProp n m ).

Definition Z2 := Z // R2Z.

(* Even though Z fits in Set, it is not the case of Z/2Z which should be smaller (bool : Set!) *)
Fail Check Z2 : Set.

(* Alternative definition of Z2 (ie bool) *)
Inductive Z2' : Set := c0 | c1.

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

(* Random exercise *)
Goal forall x : True, forall e : heq x x, heq e (heq_refl _).
Proof.
  destruct x.
  inversion e.
Abort.

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
  assert (eq (n-1) (2*k))%Z.
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


Let f (x : Z2') : Z2.
Proof.
  destruct x.
  - exists (fun z => exist _ (even z) (evenhProp z)).
    compute.
    apply tr.
    exists 0%Z.
    intro y.
    exists (g y).
    split.
    + exists (h y).
      apply hg_id.
    + exists (h y).
      apply gh_id.
  - exists (fun z => exist _ (odd z) (oddhProp z)).
    compute.
    apply tr.
    exists 1%Z.
    intro y.
    exists (g2 y) ; split.
    + exists (h2 y) ; apply h2g2_id.
    + exists (h2 y) ; apply g2h2_id.
Defined.

Axiom ff : forall X, X.

Set Printing Universes.
Fixpoint foo (n : nat) : Z2.
destruct n.
- exact (f c1).
- Fail simple refine (exist _ (fun z => (forall x : Z2, heq x (foo n) -> let (P, _) := x in pi1 (P z); _)) _).
  (*+ apply ff.
  + apply ff.
Defined.*)
Abort.

(*
Lemma eq_to_heq {A} : forall x y : A, eq x y -> heq x y.
Proof.
  intros x y eq.
  now destruct eq.
Defined.

(*! WARNING : use of omega AND Defined !*)
Lemma either_even_odd : forall z, hsum (exists k, heq z (2 * k)%Z) (exists k, heq z (2 * k + 1)%Z).
Proof.
  intro z.
  destruct z.
  - left. exists 0%Z. now compute.
  - destruct p.
    + right ; exists (Z.pos p) ; pose proof (Pos2Z.inj_xI p) ; easy.
    + left ; exists (Z.pos p) ; pose proof (Pos2Z.inj_xO p) ; easy.
    + right. exists 0%Z. now simpl.
  - destruct p.
    + right. exists (Z.neg p - 1)%Z. pose proof (Pos2Z.neg_xI p). apply eq_to_heq. omega.
    + left. exists (Z.neg p). pose proof (Pos2Z.neg_xO p). easy.
    + right. exists (-1)%Z. now simpl.
Defined.

Lemma even_odd_false : forall m k l, heq m (2 * k)%Z -> heq m (2 * l + 1)%Z -> False.
Proof.
  intros m k l even odd.
  rewrite odd in even.
  destruct k ; destruct l ;
  try (simpl in even ; easy).
  induction p0 ; try easy.
Defined.

Lemma inv_hProp : forall {A}, ishProp A -> forall x y : A, contractible (heq x y).
Proof.
  intros A h x y.
  inversion h.
  pose proof (X x y).
  now inversion X0.
Defined.

Axiom fun_ext : forall {A B} {f g : A -> B}, (forall x, heq (f x) (g x)) -> heq f g.

Lemma hsum_hProp : forall A, ishProp A -> ishProp (hsum A (A -> False)).
Proof.
  intros A h.
  apply hsuc.
  intros x y.
  apply hctr.
  assert (heq x y).
  - destruct x ; destruct y ; try easy.
    + pose proof (inv_hProp h a a0).
      destruct X as [p eq].
      now destruct p.
    + apply hf_equal.
      apply fun_ext.
      intro x.
      destruct (b x).
  - destruct X.
    exists (heq_refl _).
    intro p.
    apply eq_proofs_unicity.
    intros a b. destruct a ; destruct b ; try easy.
    + left.
      pose proof (inv_hProp h a a0).
      destruct X as [q eq].
      now destruct q.
    + left.
      apply hf_equal.
       apply fun_ext.
      intro tutu.
      destruct (b tutu).
Defined.

(*! WARNING : use of omega AND Defined !*)

Set Printing Universes.


Lemma either_in : forall (z : Z) (P : Z -> hProp) (h : trunc minus1 (isEqClass R2Z P)),
                    hsum (pi1 (P z)) (pi1 (P z) -> False).
Proof.
  intros z P h.
  refine (trunc_ind (fun aa => _) _ h).
  - intro hh.
    apply hsum_hProp.
    now destruct (P z).
  - intro p.
    destruct p as [a p].
    destruct (either_even_odd a) as [[k evena] | [k odda]] ;
      destruct (either_even_odd z) as [[l evenz] | [l oddz]].
    + left. apply p. apply (diff_even _ _ (l - k)%Z). inversion evena. inversion evenz.
      apply eq_to_heq. omega.
    + right. intro absurd. destruct (p z) as [f [[g gf] [g' g'f]]].
      destruct (g absurd) as [n m q eq].
      eapply (even_odd_false (m - n)%Z q (l - k)%Z).
      * exact eq.
      * apply eq_to_heq. inversion evena. inversion oddz. omega.
    + right. intro absurd. destruct (p z) as [f [[g gf] [g' g'f]]].
      destruct (g absurd) as [n m q eq].
      eapply (even_odd_false (m - n)%Z q (l - k - 1)%Z).
      * exact eq.
      * apply eq_to_heq. inversion evenz. inversion odda. omega.
    + left. apply p. apply (diff_even _ _ (l - k)%Z). inversion odda. inversion oddz.
      apply eq_to_heq. omega.
Defined.

Let ff (x : Z2) : Z2'.
  destruct x as [P h].
  pose (either_in 0%Z P h).
  destruct (either_in 0%Z P h).
  - exact c0.
  - exact c1.
Defined.

Class Decidable (A : Type) :=
  dec : hsum A (A -> False).
Arguments dec A {_}.

(* Two classes that share an element are equal *)
Lemma classes_share_eq :
  forall {A R} (a : A) (P Q : A -> hProp) (hp : trunc minus1 (isEqClass R P)) (hq : trunc minus1 (isEqClass R Q)),
    (forall x y, Decidable (pi1 (R x y))) -> isEqRel R -> pi1 (P a) -> pi1 (Q a) -> heq P Q.
Proof.
  intros A R a P Q hp hq dec eqrel pa qa.
  apply fun_ext.
  intro x.
  destruct eqrel as [rho sigma tau].
  destruct (dec x a).
  - assert (pi1 (P x)) as px.
    + refine (trunc_ind (fun aa => _) _ hp).
      * intro hp'. now destruct (P x).
      * intro hpp. destruct hpp as [e h]. apply h.
        { apply (tau _ a).
          - now apply sigma.
          - now apply h.
        }
    + assert (pi1 (Q x)) as qx.
      * { refine (trunc_ind (fun aa => _) _ hq).
          - intro hq'. now destruct (Q x).
          - intro hqq. destruct hqq as [e h]. apply h.
            apply (tau _ a).
            + now apply sigma.
            + now apply h.
        }
      * admit.
  - assert (pi1 (P x) -> False) as npx.
    + intro px. apply b.
      refine (trunc_ind (fun aa => _) _ hp).
      * intro hp'. now destruct (R x a).
      * intro hpp. destruct hpp as [e h].
        { apply (tau _ e).
          - now apply h.
          - apply sigma. now apply h.
        }
    + assert (pi1 (Q x) -> False) as nqx.
      * intro qx. apply b.
        { refine (trunc_ind (fun aa => _) _ hq).
          - intro hq'. now destruct (R x a).
          - intro hqq. destruct hqq as [e h].
            apply (tau _ e).
            + now apply h.
            + apply sigma. now apply h.
        }
      *

Lemma equiv_bool_Z2 : isEquiv f.
Proof.
  split.
  - exists ff. intro a. unfold comp. unfold id. destruct a ;
    unfold f ; unfold ff ; now simpl.
  - exists ff. intro a. unfold comp. unfold id. destruct a as [P h].
    unfold ff. destruct (either_in 0%Z P h).
    + unfold f. (* We probably need something to say that two equivalence classes that share an element are equal. *)
*)
