Set Printing Universes.
Set Universe Polymorphism.
Set Primitive Projections.

Add LoadPath "../quotient".
Require Import Base.
Require Import MyEqDepDec.

(*! Contractible types *)

(* Unset Printing Notations. *)

Record contractible@{i} (T : Type@{i}) : Type@{i} := CtrMk
  { Point : T ;
    Ctr   : forall t : T, heq@{i i} t Point }.

(*! Integers for h-levels *)

Inductive hlevel :=
| minus2 : hlevel
| suc    : hlevel -> hlevel.

Definition minus1 := suc minus2.
Definition zero   := suc minus1.

Notation "-2" := (minus2) (at level 0).
Notation "-1" := (minus1) (at level 0).
Notation "0"  := (zero).

(*! is-n-Type *)

Fixpoint ishType@{i} (n : hlevel) (T : Type@{i}) : Type@{i} :=
  match n with
  | minus2 => contractible@{i} T
  | suc n  => forall x y : T, ishType@{i} n (heq@{i i} x y)
  end.

Definition hctr : forall T, contractible T -> ishType (-2) T.
  intros T h. exact h.
Defined.

Definition hsuc : forall l T, (forall x y : T, ishType l (heq x y)) -> ishType (suc l) T.
  intros l T h. simpl. exact h.
Defined.

Notation "is- N -Type" := (ishType N) (at level 80).

Definition ishProp := is-(-1)-Type.
Definition ishSet  := is-0-Type.

(*! n-Type *)

Definition hType (n : hlevel) := { T : Type | is-n-Type T }.

Notation "n -Type" := (hType n) (at level 75).

Definition hProp := (-1)-Type.
Definition hSet  := 0-Type.

(*! Resizing Rules for hType *)

Definition pi1 : hProp -> Type :=
  fun P => let (T,_) := P in T.

ON Unsafe Universes.

Section RR1.

  Universes i j.

  Record RR1 (A : Type@{i}) (h : ishProp@{i} A) : Type@{j} := { rr : A }.

End RR1.

OFF Unsafe Universes.

Arguments rr {_ _} r.

Definition box {A} {h : ishProp A} (a : A) : RR1 A h := Build_RR1 A h a.
Definition unbox {A} {h : ishProp A} (a : RR1 A h) : A := a.(rr).

Lemma box_unbox {A} {h : ishProp A} (x : RR1 A h) : heq (box (unbox x)) x.
  reflexivity.
Defined.

Lemma unbox_box {A} {h : ishProp A} (x : A) : heq (@unbox A h (box x)) x.
  reflexivity.
Defined.

Definition concat_Vp {A : Type} {x y : A} (p : heq x y) : heq (heq_trans _ _ _ p (heq_sym _ _ p)) (heq_refl _) :=
  match p with heq_refl _ => heq_refl _ end.

Definition path_contr {A} (h : contractible A) (x y : A) : heq x y :=
  heq_trans _ _ _ (Ctr _ h x) (heq_sym _ _ (Ctr _ h y)).

Lemma path2_contr (A : Type) (h : contractible A) (x y : A) (p q : heq x y) : heq p q.
  assert (K : forall (r : heq x y), heq r (path_contr h x y)).
  - intro r ; destruct r ; symmetry ; unfold path_contr ; now apply concat_Vp.
  - eapply (heq_trans _ (path_contr h x y)).
    + easy.
    + easy.
Defined.

Lemma contr_paths_contr : forall (A : Type) (h : contractible A) (x y : A), contractible (heq x y).
  intros A h x y. destruct h as [c ctr].
  refine ({| Point := (heq_trans _ _ _ (ctr x) (heq_sym _ _ (ctr y))) ; Ctr := _ |}).
  symmetry. apply path2_contr. exact {| Point := c ; Ctr := ctr |}.
Defined.

Lemma hProp_allpath (A : Type) : (forall (x y : A), heq x y) -> ishProp A.
  intros h x y.
  assert (forall x y : A, heq y x) as h'.
  - intros a b. apply h.
  - pose (C := CtrMk A x (h' x)).
    now apply contr_paths_contr.
Defined.

Lemma RR1_hProp : forall (A : Type) (h : ishProp A), ishProp (RR1 A h).
  intros A h. apply hProp_allpath. intros x y.
  destruct x as [x] ; destruct y as [y]. destruct (h x y) as [p _].
  now destruct p.
Defined.

(*! Truncation *)

Module Export Truncation.

  Private Inductive trunc (n : hlevel) (A : Type) : Type :=
  | tr : A -> trunc n A.
  Bind Scope trunc_scope with trunc.
  Arguments tr {n A} a.

  Section Foo.

    Universes i.

    Global Lemma ishType_trunc (n : hlevel) (A : Type@{i})
    : ishType@{i} n (trunc@{i} n A).
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

Notation "|| A ||" := (trunc minus1 A) (at level 85).

(*! Equivalence *)

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

(*! Equivalence relations *)

(* Definition pi1 (T : hProp) : Type := *)
(*   let (TT, _) := T in TT. *)

Record isEqRel {A} (R : A -> A -> hProp) :=
  { rho : forall x : A, pi1 (R x x) ;
    sigma : forall x y : A, pi1 (R x y) -> pi1 (R y x) ;
    tau : forall x y z : A, pi1 (R y z) -> pi1 (R x y) -> pi1 (R x z) }.

(*! Quotient *)

Definition isEqClass {A} (R : A -> A -> hProp) (P : A -> hProp) :=
  { x : A | forall y : A,  { f : pi1 (R x y) -> pi1 (P y) | isEquiv f } }.

(*! hProp can be inverted *)
Lemma inv_hProp {T} : ishProp T -> forall a b : T, contractible (heq a b).
Proof.
  intros h a b.
  apply h.
Defined.

(*! hProp is only up to codomain *)

Lemma forall_hProp {A B} : (forall x : A, ishProp (B x)) -> ishProp (forall x, B x).
Proof.
  intro h.
  apply hsuc. intros f g.
  apply hctr.
  assert (heq f g) as f_g.
  - apply dep_fun_ext. intro a.
    pose proof (h a) as ha.
    apply ha.
  - destruct f_g.
    exists (heq_refl _). intro p.
    apply eq_proofs_unicity. intros g1 g2.
    left. apply dep_fun_ext. intro a.
    pose proof (h a) as ha.
    apply ha.
Defined.

  