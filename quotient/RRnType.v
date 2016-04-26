Set Printing Universes.
Set Universe Polymorphism.

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

Axiom RR1 : forall (P : hProp), hProp.
(* Axiom RR1_1 : forall {P : hProp}, heq (RR1 P).1 P.1. *)
(* Unset Printing Notations. *)
Axiom RR1_1@{i j k l m maxil} :
  forall {P : hProp@{maxil j}},
    heq@{i k} (π1@{l m} (fun T : Type@{l} => ishType@{l} (-1) T) (RR1@{i j l m} P)) (π1@{i j} (fun T : Type@{i} => ishType@{i} (-1) T) P).
(* Axiom RR1_1@{i j k l m n w p q r s t u v} : *)
(*   forall {P : hProp@{i j}}, *)
(*     heq@{k l} (π1@{m n} (fun T : Type@{w} => ishType@{w} (-1) T) (RR1@{p q r s} P)) (π1@{t u} (fun T : Type@{v} => ishType@{v} (-1) T) P). *)
(* The problem here is that it equates the universes of P and RR P, so basically it was all for nothing... *)

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

Definition pi1 (T : hProp) : Type :=
  let (TT, _) := T in TT.

Record isEqRel {A} (R : A -> A -> hProp) :=
  { rho : forall x : A, pi1 (R x x) ;
    sigma : forall x y : A, pi1 (R x y) -> pi1 (R y x) ;
    tau : forall x y z : A, pi1 (R y z) -> pi1 (R x y) -> pi1 (R x z) }.

(*! Quotient *)

Definition isEqClass {A} (R : A -> A -> hProp) (P : A -> hProp) :=
  { x : A | forall y : A,  { f : (R x y).1 -> (P y).1 | isEquiv f } }.

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

  