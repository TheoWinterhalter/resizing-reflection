Set Universe Polymorphism.

Definition ishProp A := forall x y : A, x = y.

Definition comp {A B C} (f : B -> C) (g : A -> B) := fun x => f (g x).
Notation "f ∘ g" := (comp f g) (at level 86).

Definition homo {A B} (f g : A -> B) := forall a : A, (f a) = (g a).
Notation "f ~ g" := (homo f g) (at level 87).

Definition id A := fun x : A => x.

Definition isEquiv {A B} (f : A -> B) :=
  { g : B -> A & (f ∘ g ~ id B) /\ (g ∘ f ~ id A) }.

Definition Equiv A B :=
  { f : A -> B & isEquiv f }.

Notation "( x ; y )" := (existT _ x y) : core_scope.

Module Export Truncation.

  Definition trunc (A : Type) : Prop := exists _ : A , True. 
  Definition tr A : A -> trunc A. intro a. exists a. exact I. Defined.
  Arguments tr {A} a.
  (* If I can justify I can eliminate it into hProp this can be a model. *)
  (* I would also need Prop to be proof-irrelevant (which is admissible) in order
     not to need the ishProp_truc axiom. *)

  (* Private Inductive trunc (A : Type) : Prop := *)
  (* | tr : A -> trunc A. *)
  (* Bind Scope trunc_scope with trunc. *)
  (* Arguments tr {A} a. *)

  Global Lemma ishProp_trunc (A : Type) : ishProp (trunc A).
  Admitted.

  Definition trunc_rect {A} (P : trunc A -> Type) {Pt : forall aa, ishProp (P aa)}
  : (forall a, P (tr a)) -> (forall aa, P aa).
    intros f aa.
  Admitted.

    
    (* := fun f aa => *)
    (*     match aa with *)
    (*         tr a => fun _ => f a *)
    (*     end *)
    (*       Pt. *)

End Truncation.
Import Truncation.

Notation "|| A ||" := (trunc A) (at level 85).



