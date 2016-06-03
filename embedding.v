Set Universe Polymorphism.
(* Set Printing Universes. *)
Set Primitive Projections.

Definition ap {A} {B} (f : A -> B) {x y : A} (p : x = y) : f x = f y :=
  match p with eq_refl => eq_refl end.

Definition isEquiv {A} {B} (f : A -> B) : Prop :=
  exists g : B -> A, exists eta : (forall x, g (f x) = x), (forall y, f (g y) = y).

Record emb A B :=
  { ff : A -> B ;
    ef : forall (x y : A), isEquiv (ap ff (x := x) (y := y)) }.
Arguments ff {A} {B} e _.

Definition isInImg {A} {B} (f : emb A B) (b : B) : Prop :=
  exists a : A, ff f a = b.

Definition im@{i j k l} {A : Type@{i}} {B : Type@{j}} (f : emb@{i j k l} A B) : Type@{j} :=
  { b : B & isInImg f b }.

Definition fib {A} {B} (f : A -> B) (y : B) :=
  { x : A | f x = y }.

Record contr A : Prop := Buildcontr
  { point : A ;
    ptctr : forall x : A, point = x }.

Section Equiv.

  Universes i j k l.
  Variable A : Type@{i}.
  Variable B : Type@{j}.
  Variable f : emb@{i j k l} A B.

  Definition inj : A -> im f.
    intro a. exists (ff f a).
    exists a. reflexivity.
  Defined.

  Definition injEquiv : forall b : im f, contr (fib inj b).
    intro b. destruct b as [b [a h]].
    simple refine (Buildcontr _ (exist _ a _) _).
    - simpl. unfold inj. now destruct h.
    - intro x. destruct h. destruct x. unfold inj in e.

    
End Equiv.


