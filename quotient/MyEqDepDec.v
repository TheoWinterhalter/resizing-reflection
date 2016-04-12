Set Printing Universes.
Set Universe Polymorphism.

Add LoadPath "../quotient".
Require Import Base.

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