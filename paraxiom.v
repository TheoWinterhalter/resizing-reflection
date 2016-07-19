Set Primitive Projections.

Axiom param : forall p : Type = Type, p = eq_refl.

(* Record heq := Heq *)
(*   { typ : Type ; *)
(*     pnt : typ }. *)

Definition Heq (T : Type) (P : T) : { typ : Type & typ }.
  exists T. exact P.
Defined.

Lemma typeq : forall A B (p : Heq Type A = Heq Type B), A = B.
  intros A B p.
Admitted.

(* Definition transport : forall A B (p : Heq Type A = Heq Type B), A -> B. *)
(*   intros A B p a. *)
(*   inversion p. *)

Axiom funext : forall {A B} {f g : forall a : A, B a}, (forall a, (f a) = (g a)) -> f = g.

Goal forall A A' B B' (p : Heq Type A = Heq Type A')
       (q : forall (x : A) (y : A') (e : Heq A x = Heq A' y),
              Heq Type (B x) = Heq Type (B' y)),
       Heq Type (forall x:A, B x) = Heq Type (forall y:A', B' y).
Proof.
  intros A A' B B' p q.
  assert (e : (forall x : A, B x) = (forall y : A', B' y)).
  { cut (A = A').
    - intro. subst.
      cut (forall x : A', B x = B' x).
      + intro h. pose proof (funext h) as h'. now subst.
      + intro x.
        assert (e : Heq A' x = Heq A' x) by easy.
        pose proof (q x x e). now apply typeq.
    - now apply typeq.
  }
  admit.
Admitted.



