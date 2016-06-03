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

Section Equiv.

  Universes i j k l.
  Variable A : Type@{i}.
  Variable B : Type@{j}.
  Variable f : emb@{i j k l} A B.

  Definition inj : A -> im f.
    intro a. exists (ff f a).
    exists a. reflexivity.
  Defined.

  Definition proj : im f -> A.
    intros b. destruct b.
    (* The problem is here, we can't destruct on the proof to get A in Type. *)

  Definition injEquiv : isEquiv inj.
    

    
End Equiv.


