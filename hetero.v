(* Set Universe Polymorphism. *)

Inductive Id (A : Type) (x : A) : A -> Type :=
| refl : Id A x x
.

Arguments Id {A} x y.
Arguments refl {A} x.

Inductive Id2 : forall (A B : Type), A -> B -> Type :=
| refl2 : forall A a, Id2 A A a a
.

Arguments Id2 {A} {B} a b.
Arguments refl2 {A} a.

(* Every Id proof is refl for Id2... *)
Goal forall (A : Type) (B : Type) (p : Id A B),
       @Id2 _ (Id A A) p (refl A).
Proof.
  intros A B p. destruct p. apply refl2.
Qed.

Definition trans (A B : Type) (p : Id A B) : A -> B.
  destruct p. exact (fun x => x).
Defined.
Arguments trans {A} {B} p t.

(* Seems that as long as the equality remains homogenous it verifies this. *)
Goal forall (A : Type) (B : Type) (p : Id A B),
       (* @Id2 _ (Id A A) p (refl A) -> *)
       forall t : A, Id2 (trans p t) t.
Proof.
  intros A B p (*α*) t.
  destruct p. apply refl2.
Qed.

(* The problem is indeed the JMLeibniz property... *)

Set Printing Universes.
Definition trans2@{i} (A B : Type@{i}) (p : @Id2 Type@{i} Type@{i} A B) : A -> B.
  destruct p. exact (fun x => x).
Defined.

(* Goal forall (A B : Type) (p : I) *)


