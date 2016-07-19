(* To use with HoTT *)
Require Import HoTT.

Set Primitive Projections.

Axiom param : forall p : Type = Type, p = idpath.

Definition Heq (T : Type) (P : T) : { typ : Type & typ }.
  exists T. exact P.
Defined.

(* We deduce it from the axiom. *)
Lemma typeq : forall A B (p : Heq Type A = Heq Type B), A = B.
  intros A B p.
Admitted.

Axiom funext : forall {A B} {f g : forall a : A, B a}, (forall a, (f a) = (g a)) -> f = g.

Goal forall (U : Univalence)
       A1 A2 B1 B2 f1 f2 u1 u2
       (pf : Heq (A1 -> B1) f1 = Heq (A2 -> B2) f2)
       (pu : Heq A1 u1 = Heq A2 u2),
       Heq B1 (f1 u1) = Heq B2 (f2 u2).
Proof.
  intros U A1 A2 B1 B2 f1 f2 u1 u2 pf pu.
  simple refine (path_sigma _ _ _ _ _).
  - simpl. assert (h : A1 = A2) by apply pu..1. destruct h. rename A1 into A.
    assert (h : u1 = u2) by admit. destruct h. rename u1 into u.
    pose (p := pf ..1). simpl in p.
    pose (f := fun (b : B1) => (transport idmap p (fun y : A => b)) u).
    simple refine (@path_universe U _ _ f _).
    pose (g := fun (b : B2) => (transport idmap p^ (fun y : A => b)) u).
    simple refine (BuildIsEquiv _ _ _ g _ _ _).
    + intro b. unfold g. unfold f. admit.
  (* - admit. *)
Abort.

Goal forall (U : Univalence)
       A1 A2 B1 B2 f1 f2 u1 u2
       (pf : Heq (forall x:A1, B1 x) f1 = Heq (forall x:A2, B2 x) f2)
       (pu : Heq A1 u1 = Heq A2 u2),
       Heq (B1 u1) (f1 u1) = Heq (B2 u2) (f2 u2).
Proof.
  intros U A1 A2 B1 B2 f1 f2 u1 u2 pf pu.
  simple refine (path_sigma _ _ _ _ _).
  - simpl. assert (h : A1 = A2) by apply pu..1. destruct h. rename A1 into A.
    (* pose (pu..2). simpl in p. *)
    assert (h : u1 = u2) by admit. destruct h. rename u1 into u.
    pose (p := pf ..1). simpl in p.
  (*   pose (f := fun (b : B1 u) => (transport idmap p (fun y : A => b)) u). *)
  (*   apply (path_universe f). *)
  (* - admit. *)
Abort.

Goal forall A A' B B' (p : Heq Type A = Heq Type A')
       (q : forall (x : A) (y : A') (e : Heq A x = Heq A' y),
              Heq Type (B x) = Heq Type (B' y)),
       Heq Type (forall x:A, B x) = Heq Type (forall y:A', B' y).
Proof.
  intros A A' B B' p q.
  assert (e : (forall x : A, B x) = (forall y : A', B' y)).
  { cut (A = A').
    - intro. destruct X.
      cut (forall x : A, B x = B' x).
      + intro h. pose proof (funext h) as h'. destruct h'. reflexivity.
      + intro x.
        assert (e : Heq A x = Heq A x).
        { reflexivity. }
        pose proof (q x x e). apply typeq. apply X.
    - apply typeq. apply p.
  }
  unfold Heq.
  simple refine (path_sigma _ _ _ _ _).
  - exact idpath.
  - simpl. exact e.
Qed.



