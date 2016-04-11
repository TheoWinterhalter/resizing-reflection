Set Printing Universes.
Set Universe Polymorphism.

Require Import Quotient.Base.

(* Rewriting Rule *)

Axiom RR1 : forall (A : Type), ishProp A -> Set.

(* This produces the annoying n < m <= i *)
(* It's alright because we need RR2 to state that hProp : Set *)
Require Import Coq.Program.Tactics.
Program Definition quotient@{i j k l m n p q r s e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16} (A : Type@{i}) (R : A -> A -> hProp@{j k l}) : Type@{i}
  := { P : A -> hProp@{m n r} | RR1@{p q} (trunc@{s} minus1 (isEqClass@{e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16} R P)) _ }.
Next Obligation.
  apply ishType_trunc.
Defined.

Notation "A // R" := (quotient A R) (at level 90).

(* Let's try it with Z/2Z *)

Require Import ZArith.

Inductive R2Ztype : Z -> Z -> Type :=
| diff_even : forall n m k, heq (n - m)%Z (2 * k)%Z -> R2Ztype n m.

Require Eqdep_dec.

Section MyEqdepDec.

  Variable A : Type.

  Let comp (x y y' : A) (eq1 : heq x y) (eq2 : heq x y') : heq y y'.
  Proof.
    induction eq1.
    exact eq2.
  Defined.

  Remark trans_sym_eq : forall (x y : A) (u : heq x y), heq (comp _ _ _ u u) (heq_refl y).
  Proof.
    intros x y u.
    now induction u.
  Defined.

  Variable x : A.

  Inductive hsum (A : Type) (B : Type) :=
  | inl : forall a : A, hsum A B
  | inr : forall b : B, hsum A B.

  Variable eq_dec : forall y : A, hsum (heq x y) ((heq x y) -> False).

  Let nu (y : A) (u : heq x y) : heq x y :=
    match eq_dec y with
      | inl _ _ eqxy => eqxy
      | inr _ _ neqxy => False_rect _ (neqxy u)
    end.

  Let nu_constant : forall (y : A) (u v : heq x y), heq (nu _ u) (nu _ v).
  Proof.
    intros y u v.
    compute.
    case (eq_dec y).
    - now intro a.
    - intro b.
      exfalso.
      apply b.
      exact u.
  Defined.

  Let nu_inv (y : A) (v : heq x y) : heq x y := comp _ _ _ (nu _ (heq_refl x)) v.

  Remark nu_left_inv_on : forall (y : A) (u : heq x y), heq (nu_inv _ (nu _ u)) u.
  Proof.
    intros y u.
    compute.
    destruct u.
    apply trans_sym_eq.
  Defined.

  Theorem eq_proofs_unicity_on : forall (y : A) (p1 p2 : heq x y), heq p1 p2.
  Proof.
    intros y p1 p2.
    eapply (heq_rect _ (nu_inv y (nu y p1)) (fun (p3 : heq x y) _ => heq p3 p2)).
    - eapply (heq_rect _ (nu_inv y (nu y p2)) (fun (p3 : heq x y) _ => heq (nu_inv y (nu y p1)) p3)).
      + eapply (heq_rect _ (nu y p1) (fun (e : heq x y) _ => heq (nu_inv y (nu y p1)) (nu_inv y e))).
        * apply heq_refl.
        * apply nu_constant.
      + eapply nu_left_inv_on.
    - apply nu_left_inv_on.
  Defined.

End MyEqdepDec.

Definition eq_proofs_unicity (A : Type) (eq_dec : forall x y : A, hsum (heq x y) ((heq x y) -> False)) (x : A)
: forall (y : A) (p1 p2 : heq x y), heq p1 p2.
Proof.
  intros y p1 p2.
  apply eq_proofs_unicity_on.
  apply (eq_dec x).
Defined.

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

Lemma R2ZhProp : forall n m, ishType minus1 (R2Ztype n m).
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
      now apply (division_unicity (n - m)%Z).
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

(* This time, we still don't have Z2 : Set because we would need RR2 to do so, but as pointed out in the definitin of
   quotient, we would keep the same universe if not for hProp being to big for Set. *)
Fail Check Z2 : Set.

(* In order to show we can still manipulate Z2 even though RR1 is inside, we will show that it is equivalent to bool. *)
