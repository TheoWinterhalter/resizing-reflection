Set Printing Universes.
Set Universe Polymorphism.

Require Import ZArith.
Open Scope Z_scope.

(* Contractible types *)

Record contractible (T : Type) := CtrMk
  { Point : T ;
    Ctr   : forall t : T, t = Point }.

(* Polymorhpic equality *)

Inductive peq {A : Type} (x : A) : A -> Type :=
  peq_refl : peq x x.

Notation "A ?= B" := (peq A B).

(* Trunc *)

Inductive isTrunc@{i j} : Z -> Type@{i} -> Type@{j} :=
| trunc_ctr : forall T : Type@{i}, contractible T -> isTrunc (-2) T
| trunc_suc : forall (m : Z) (T : Type@{i}), (forall x y : T, isTrunc m (peq@{i i} x y)) ->
                                        isTrunc (m+1) T.

Record Trunc (n : Z) := TruncMk
  { truncT : Type ;
    truncP : isTrunc n truncT }.

(* Equivalence *)

Record isEquiv A B (f : A -> B) :=
  { eq_g : B -> A ;
    eta    : forall b : B, f (eq_g b) = b ;
    epsilon    : forall a : A, eq_g (f a) = a (*;
    alpha    : *)}.

Record Equiv A B :=
  { eqv_f : A -> B ;
    eqv_p : isEquiv A B eqv_f }.

(* Rewriting Rule *)

Axiom rr0@{i j si} :
  forall {A : Type@{i}} (B : Type@{j}),
  forall {p : Equiv A B} {q : isTrunc@{i si} (-1) A},
    Type@{i}.

(* Somethinng that works in Prop *)

Parameter P : Prop -> Prop.

Fixpoint Pn (n : nat) : Prop :=
  match n with
  | O   => True
  | S m => P (Pn m)
  end.

(* But not in Type *)

Parameter T@{i j} : let _ := Type@{i} : Type@{j} in Type@{i} -> Type@{j}.

(*Fixpoint Tn (n : nat) : Type :=
  match n with
  | O   => True
  | S m => T (Tn m)
  end.*)

(* It might be nice to find an actual instance that could come with Types, but also
   Prop, depending.
   The point is then to use hProp instead, and show it would work with the rewriting
   rule rr0 as if it was in Prop. *)

(* True is hProp *)
Lemma hPropTrue : isTrunc (-1) True.
Proof.
  apply (trunc_suc (-2)).
  intros x y.
  apply trunc_ctr.
  destruct x.
  destruct y.
  exists (peq_refl I).
  intro p.
Admitted.

Lemma step : forall Tm : Trunc (-1), isTrunc (-1) (T (truncT _ Tm)).
Proof.
  intro Tm.
  apply (trunc_suc (-2)).
  intros x y.
  apply trunc_ctr.
  destruct Tm as [Tm p].
Admitted.

Fixpoint Tn (n : nat) : Trunc (-1) :=
  match n with
  | O   => TruncMk (-1) True hPropTrue 
  | S m =>
    let Tm := Tn m in
    TruncMk (-1) (T (truncT _ Tm)) (step Tm)
  end.






