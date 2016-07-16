Set Universe Polymorphism.

Inductive Id (A : Type) (x : A) : A -> Type :=
| refl : Id A x x
.

Arguments Id {A} x y.
Arguments refl {A} x.

Inductive Id2 (A : Type) (a : A) : forall (B : Type), B -> Type :=
| refl2 : Id2 A a A a
.

Arguments Id2 {A} a {B} b.
Arguments refl2 {A} a.

(* Every Id proof is refl for Id2... *)
Goal forall (A : Type) (B : Type) (p : Id A B),
       @Id2 _ p (Id A A) (refl A).
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

(* The problem for transport is that the quantified B is not
   necessarilly a type. *)
(* Definition trans2 (A B : Type) (p : Id2 A B) : A -> B := *)
(*   Id2_rect Type A *)
(*            (fun (T : Type) (B : T) (p : Id2 A B) => *)
(*               forall (e : Id T Type), Id A (trans e B) -> A -> trans e B) *)
(*            (fun e f a => trans f a) Type B p (refl _) _ *)
(* . *)

(* Goal forall (A B : Type) (p : I) *)

(* Some other tests *)

Definition cons {A : Type} {x y z : A} (p : Id x y) (q : Id y z) : Id x z.
  destruct p. exact q.
Defined.

Goal forall T (t u : T) (q1 : Id t u) (q2 : Id u t),
       Id (refl t) (cons q1 q2).
Proof.
  intros T t u q1 q2.
  destruct q1. simpl.
  (* We have what we want. *)
Abort.

Definition π {A A' : Type} {B : A -> Type} {B' : A' -> Type}
             (p : Id A A') (q : Id B (fun x : A => B' (trans p x)))
           : Id (forall x:A, B x) (forall x:A', B' x).
Proof.
  destruct p. simpl in q. now inversion q.
Defined.

Goal forall A (B : A -> Type) (q1 : Id A A) (q2 : Id B (fun x : A => B (trans q1 x))),
       Id (refl (forall x:A, B x)) (π q1 q2).
Proof.
  intros A B q1.
  cut (q1 = refl A).
  - intro h. rewrite h. intro q2.
    simpl in q2.
    cut (q2 = refl B).
    + intro h2. rewrite h2. reflexivity.
    + admit.
  - admit.
Admitted.


