Set Printing Universes.
Set Universe Polymorphism.

Add LoadPath "../quotient".
Require Import Base.
Require Import MyEqDepDec.

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

Fixpoint _ishType (n : hlevel) (T : Type) : Type :=
  match n with
  | minus2 => contractible T
  | suc n  => forall x y : T, _ishType n (heq x y)
  end.

Lemma nType_hProp : forall n T, _ishType minus1 (_ishType n T).
Proof.
  intro n ; induction n as [| n ihn] ; intro T.
  - intros x y. simpl in x,y. simpl.
    assert (heq x y) as x_y.
    + destruct x as [px hx] ; destruct y as [py hy].
      assert (heq px py) as px_py.
      * now apply hy.
      * destruct px_py.
        { assert (heq hx hy) as hx_hy.
          - apply dep_fun_ext. intro a.
            apply eq_proofs_unicity.
            intros x y.
            left. apply (heq_trans _ px).
            + now apply hx.
            + apply heq_sym ; now apply hx.
          - now destruct hx_hy.
        }
    + destruct x_y.
      exists (heq_refl _). intro p.
      apply eq_proofs_unicity. intros a b. left.
      destruct a as [pa ha] ; destruct b as [pb hb].
      assert (heq pa pb) as pa_pb.
      * now apply hb.
      * destruct pa_pb.
        { assert (heq ha hb) as ha_hb.
          - apply dep_fun_ext. intro u.
            apply eq_proofs_unicity. intros v w.
            left. apply (heq_trans _ pa).
            + now apply ha.
            + apply heq_sym. now apply ha.
          - now destruct ha_hb.
        }
  - 

Lemma nType_hProp : forall n T, _ishType minus1 (_ishType n T).
Proof.
  intros n T.
  intros x y.
  assert (heq x y).
  - induction n.
    + simpl in x,y.
      destruct x as [px hx] ; destruct y as [py hy].
      assert (heq px py) as px_py.
      * now apply hy.
      * destruct px_py.
        { assert (heq hx hy) as hx_hy.
          - apply dep_fun_ext. intro a.
            apply eq_proofs_unicity.
            intros x y.
            left. apply (heq_trans _ px).
            + now apply hx.
            + apply heq_sym ; now apply hx.
          - now destruct hx_hy.
        }
    + simpl in x,y.
      apply dep_fun_ext. intro a.
      apply dep_fun_ext. intro b.

(* Resizing Rules *)

Axiom RR1 : forall (A : Type), ishProp A -> Set.

Axiom RR1_box : forall {A : Type} {h : ishProp A} (a : A), RR1 A h.
Axiom RR1_unbox : forall {A : Type} {h : ishProp A} (a : RR1 A h), A.
Axiom RR1_unbox_box : forall {A : Type} {h : ishProp A} (a : A),
                        heq (@RR1_unbox A h (@RR1_box A h a)) a.

Axiom RR1_hProp : forall T (h : ishProp T), ishProp (RR1 T h).

(* END *)

Definition hctr : forall T, contractible T -> ishType minus2 T.
  intros T h ; exact h.
Defined.

Definition hsuc : forall l T, (forall x y : T, ishType l (heq x y)) -> ishType (suc l) T.
  intros l T h. easy.
Defined.

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

Module Export Truncation.

  Private Inductive trunc (n : hlevel) (A : Type) : Type :=
  | tr : A -> trunc n A.
  Bind Scope trunc_scope with trunc.
  Arguments tr {n A} a.

  Section Foo.

    Universes i j k l.

    Global Lemma ishType_trunc (n : hlevel) (A : Type@{i})
    : ishType@{i j k l} n (trunc@{i} n A).
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
