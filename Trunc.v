Set Universe Polymorphism.

Inductive Trunc A : Prop :=
  tr : A -> Trunc A.

Definition ishProp A := forall x y : A, x = y.

Definition comp {A B C} (f : B -> C) (g : A -> B) := fun x => f (g x).
Notation "f ∘ g" := (comp f g) (at level 86).

Definition homo {A B} (f g : A -> B) := forall a : A, (f a) = (g a).
Notation "f ~ g" := (homo f g) (at level 87).

Definition id A := fun x : A => x.

Definition isEquiv {A B} (f : A -> B) :=
  { g : B -> A & (f ∘ g ~ id B) /\ (g ∘ f ~ id A)}.

Definition Equiv A B :=
  { f : A -> B & isEquiv f }.

(* Let's try with the excluded middle *)

Section EM.

  Variable A : Type.
  Variable h : ishProp A.
  Variable EM : A + (A -> False).

  Lemma equiv : (Equiv A True) + (Equiv A False).
  Proof.
    destruct EM as [a | na].
    - left. exists (fun a => I). exists (fun t => a). split.
      + unfold comp, homo, id. intro t.
        now destruct t.
      + unfold comp, homo, id. intro b.
        apply h.
    - right. exists (fun a => na a). exists (fun f => False_rect A f). split.
      + unfold comp, homo, id. intro f.
        now destruct f.
      + unfold comp, homo, id. intro a.
        exfalso. now apply na.
  Qed.

End EM.




