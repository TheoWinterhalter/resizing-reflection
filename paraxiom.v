Axiom param : forall p : Type = Type, p = eq_refl.

Record heq := Heq
  { typ : Type ;
    pnt : typ }.

Definition transport : forall A B (p : Heq Type A = Heq Type B), A -> B.
  intros A B p a.
  inversion p.



