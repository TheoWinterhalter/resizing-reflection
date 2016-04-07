Set Printing Universes.
Set Universe Polymorphism.

(* Polymorhpic equality *)

Inductive heq {A : Type} (x : A) : A -> Type :=
  heq_refl : heq x x.

Notation "A = B" := (heq A B) (at level 70).

(* Sigma *)

Notation idmap := (fun x => x).

Notation compose := (fun g f x => g (f x)).
Notation " g 'o' f " := (compose g f) (at level 40, left associativity)
: core_scope.

Set Primitive Projections.
Record sig {A} (P : A -> Type) := exist { π1 : A ; π2 : P π1 }.
Arguments exist {_} _ _ _.
Scheme sig_rect := Induction for sig Sort Type.

Notation "{ x | P }" := (sig (fun x => P)) (only parsing) : type_scope.
Notation "{ x : A | P }" := (sig (A:=A) (fun x => P)) (only parsing) :
type_scope.
Notation "'exists' x .. y , P"
 := (sig (fun x => .. (sig (fun y => P)) ..))
      (at level 200, x binder, y binder, right associativity) : type_scope.
Notation "∃ x .. y , P"
 := (sig (fun x => .. (sig (fun y => P)) ..))
      (at level 200, x binder, y binder, right associativity) : type_scope.
Notation "( x ; y )" := (exist _ x y) : core_scope.
Notation "( x ; y ; z )" := (x ; (y ; z)) : core_scope.
(* Notation "( x ; y ; .. ; z )" := (exist _ .. (exist _ x y) .. z) :
core_scope. *)
Notation pr1 := (π1 _).
Notation pr2 := (π2 _).
Notation "x .1" := (π1 _ x) (at level 3, format "x '.1'") : core_scope.
Notation "x .2" := (π2 _ x) (at level 3, format "x '.2'") : core_scope.

Definition prod A B := sig (fun _ : A => B).
Notation "A * B" := (prod A B) (at level 40, left associativity) :
type_scope.
Notation "A × B" := (prod A B) (at level 60, right associativity) :
type_scope.
Definition pair {A B} : A -> B -> A × B := fun x y => (x; y).
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
Definition fst {A B} : A × B -> A := pr1.
Definition snd {A B} : A × B -> B := pr2.

Definition iff (A B : Type) := (A -> B) × (B -> A).
Notation "A <-> B" := (iff A B)%type : type_scope.

Definition transitive_iff {A B C}
 : A <-> B -> B <-> C -> A <-> C.
Proof.
 intros H1 H2. split; firstorder.
Defined.

(* Contractible types *)

Record contractible (T : Type) := CtrMk
  { Point : T ;
    Ctr   : forall t : T, heq t Point }.

(* Integers for h-levels *)

Inductive hlevel :=
| minus2 : hlevel
| suc    : hlevel -> hlevel.

Definition minus1 := suc minus2.
Definition zero   := suc minus1.

Notation "-2" := (minus2).
Notation "-1" := (minus1).
Notation "0"  := (zero).

(* is-n-Type *)

Inductive ishType@{i j} : hlevel -> Type@{i} -> Type@{j} :=
| hctr : forall T : Type@{i}, contractible@{i i} T -> ishType minus2 T
| hsuc : forall (l : hlevel) (T : Type@{i}),
           (forall x y : T, ishType l (heq@{i i} x y)) ->
           ishType (suc l) T.

Notation "is- N -Type" := (ishType N) (at level 80).

Goal is-minus2-Type True.
Proof.
  apply hctr.
  exists I.
  intro t ; now destruct t.
Qed.

Definition ishProp := is-minus1-Type.
Definition ishSet  := is-0-Type.

(* n-Type *)

Definition hType (n : hlevel) := { T : Type | is-n-Type T }.

Notation "n -Type" := (hType n) (at level 75).

Definition hProp := minus1-Type.
Definition hSet  := 0-Type.

(* Truncation *)

Module Truncation.

  Private Inductive trunc (n : hlevel) (A : Type) : Type :=
  | tr : A -> trunc n A.
  Bind Scope trunc_scope with trunc.
  Arguments tr {n A} a.

  Section Foo.

    Universes i j.

    Global Lemma ishType_trunc (n : hlevel) (A : Type@{i})
    : ishType@{i j} n (trunc@{i} n A).
    Admitted.

  End Foo.

  Definition trunc_ind {n A}
             (P : trunc n A -> Type) {Pt : forall aa, ishType n (P aa)}
  : (forall a, P (tr a)) -> (forall aa, P aa)
    := fun f aa =>
        match aa with
            tr a => fun _ => f a
        end
          Pt.

End Truncation.
Import Truncation.

Notation "|| A ||" := (trunc minus1 A).

(* Equivalence *)

Definition comp {A B C} (f : B -> C) (g : A -> B) := fun x => f (g x).
Notation "f ∘ g" := (comp f g) (at level 86).

Definition homo {A B} (f g : A -> B) := forall a : A, heq (f a) (g a).
Notation "f ~ g" := (homo f g) (at level 87).

Definition id A := fun x : A => x.

(*Inductive prod A B :=
| pair : forall (a : A) (b : B), prod A B.*)
Notation "A * B" := (prod A B).

Definition isEquiv {A B} (f : A -> B) :=
  { g : B -> A | g ∘ f ~ id A } * { h : B -> A | f ∘ h ~ id B }.

(* Equivalence relations *)

Definition pi1 (T : hProp) : Type :=
  let (TT, _) := T in TT.

(* I don't really like this solution with projections but that'll have to do for now. *)
Record isEqRel {A} (R : A -> A -> hProp) :=
  { rho : forall x : A, pi1 (R x x) ;
    sigma : forall x y : A, pi1 (R x y) -> pi1 (R y x) ;
    tau : forall x y z : A, pi1 (R y z) -> pi1 (R x y) -> pi1 (R x z) }.

(* Quotient *)

Definition isEqClass {A} (R : A -> A -> hProp) (P : A -> hProp) :=
  { x : A | forall y : A,  { f : pi1 (R x y) -> pi1 (P y) | isEquiv f } }.

Definition quotient A (R : A -> A -> hProp) := { P : A -> hProp | (trunc minus1 (isEqClass R P)) }.
Notation "A // R" := (quotient A R) (at level 90).

(* Let's try it with Z/2Z *)

Require Import ZArith.

Inductive R2Ztype : Z -> Z -> Type :=
| diff_even : forall n m k, heq (m - n)%Z (2 * k)%Z -> R2Ztype n m.

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

(* transitivity of heq *)
Lemma heq_trans {A} : forall a b c : A, heq a b -> heq b c -> heq a c.
Proof.
  intros a b c eqab eqbc.
  destruct eqab.
  exact eqbc.
Defined.

Lemma heq_sym {A} : forall a b : A, heq a b -> heq b a.
Proof.
  intros a b eq.
  now destruct eq.
Defined.

Unset Printing Universes.

(*Definition g : forall (y : Z), pi1 (R2Z 0%Z y) -> even y.
  intros y p.
  compute in p.
  simple refine ((R2Ztype_rect (fun x y _ => heq x 0%Z -> even y) _ _ _ p) (heq_refl _)).
  intros n m k e h.
  apply (is_even _ k).
  apply (heq_trans _ (m - 0)%Z).
  - apply heq_sym.
    apply minus0_id.
  - apply (heq_trans _ (m - n)%Z).
    + now destruct h.
    + exact e.
Defined.*)

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
  
(*Definition h : forall y, even y -> pi1 (R2Z 0%Z y).
Proof.
  intros y p.
  compute.
  destruct p.
  apply (diff_even _ _ k).
  apply (heq_trans _ n).
  - apply minus0_id.
  - exact h.
Defined.*)

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
      pose proof (inv_hProp h).
      admit.
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
      admit.
Admitted.

(*! WARNING : use of omega AND Defined !*)
Lemma either_in : forall (z : Z) (P : Z -> hProp) (h : trunc minus1 (isEqClass R2Z P)), hsum (pi1 (P z)) (pi1 (P z) -> False).
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
  

Lemma equiv_bool_Z2 : isEquiv f.
Proof.
  
    
