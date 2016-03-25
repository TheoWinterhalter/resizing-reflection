Set Printing Universes.
Set Universe Polymorphism.

Require Import ZArith.
Open Scope Z_scope.

(* Contractible types *)

Record contractible (T : Type) :=
  { Point : T ;
    Ctr   : forall t : T, t = Point }.

(* Polymorhpic equality *)

Inductive eq {A : Type} (x : A) : A -> Type :=
  eq_refl : eq x x.

Notation "A = B" := (eq A B).

(* Trunc *)

Inductive isTrunc@{i j} : Z -> Type@{i} -> Type@{j} :=
| trunc_ctr : forall T : Type@{i}, contractible T -> isTrunc (-2) T
| trunc_suc : forall (m : Z) (T : Type@{i}), (forall x y : T, isTrunc m (x = y)) ->
                                        isTrunc (m+1) T.

Record Trunc (n : Z) :=
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




