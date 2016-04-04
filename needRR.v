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

Definition hProp := Trunc (-1).

Definition ishProp := isTrunc (-1).

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
  forall {p : Equiv A B} {q : ishProp@{i si} A},
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

(* Instance *)

Inductive sum A B :=
| inl : forall a : A, sum A B
| inr : forall b : B, sum A B.

Notation "A + B" := (sum A B).

Inductive prod A B :=
| pair : forall (a : A) (b : B), prod A B.

Notation "A * B" := (prod A B).

(* An instance could be some heterogenous list *)
Record IT@{i} (A : Type@{i}) := { ITT : Type@{i} ; ITE : prod ITT A }.

(* If we don't leave universes implicit we don't really get what we want, but I guess it would be better
   if it came naturally without having to specifiy the universes at all. *)
Record IT' (A : Type) := { IT'T : Type ; IT'E : prod IT'T A }.

Example foo : IT (IT True).
Proof.
  exists Z.
  split.
  - exact 3.
  - exists nat.
    split.
    + exact (S O).
    + exact I.
Defined.

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

(*Lemma truncEquiv : forall hV p, Equiv (truncT (-1) {| truncT := hV; truncP := p |}) hV.
Proof.
  intros hV p.
  exists (fun x => x).*)

Lemma stepList : forall hVm : hProp, ishProp (IT (truncT _ hVm)).
Proof.
  intro hVm.
  apply (trunc_suc (-2)).
  intros x y.
  apply trunc_ctr.
  destruct hVm as [hV p].
  inversion p as [| minus2 hV' ctr eqminus2 hVeq] ;
  subst ;
  assert (minus2 = -2) by omega ; subst ; destruct eqminus2.
  destruct x as [Tx [x ex]].
  destruct y as [Ty [y ey]].
  simpl.
  pose proof (ctr ex ey) as h.
  inversion h as [h0 [ctre ctrp] | cccccc ddddd] ; subst.
  - admit.
  - (* This shouldn't happen because we go below -2 *)
    admit.
Admitted.

(* It would be nice to encapsulate [IT (truncT _ hVm)] into something that doesn't grow.
   Can we though? Because our definition is too artificial it might not work at all. *)

(*Fixpoint heteroVector (n : nat) : hProp :=
  match n with
  | O   => TruncMk (-1) True hPropTrue
  | S m =>
    let hVm := heteroVector m in
    TruncMk (-1)
            (rr0 (IT (truncT _ hVm))
                 ?
                 ?
                 (truncP _ hVm))
            (stepList hVm)
  end.*)

Lemma step : forall Tm : Trunc (-1), isTrunc (-1) (T (truncT _ Tm)).
Proof.
  intro Tm.
  apply (trunc_suc (-2)).
  intros x y.
  apply trunc_ctr.
  destruct Tm as [Tm p].
Admitted.

(*Fixpoint Tn (n : nat) : Trunc (-1) :=
  match n with
  | O   => TruncMk (-1) True hPropTrue
  | S m =>
    let Tm := Tn m in
    TruncMk (-1) (T (truncT _ Tm)) (step Tm)
  end.*)


(* Let's go for a type where universes are justified in a better fashion than ou previous IT.
   This time however, it isn't really something that would appear naturally, we will work on that
   afterwards. *)

Definition Too@{i si} (A : Type@{i}) : Type@{si} := forall B : Type@{i}, @peq@{si si} Type@{i} B A -> A -> B.

(* Do we have an equivalent to Too A which lives in the same universe as A? *)
Lemma smallToo :
  forall A : Type, Equiv (Too A)
