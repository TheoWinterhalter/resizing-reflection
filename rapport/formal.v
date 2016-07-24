(* You need to compile it with HoTT (from the github HoTT/HoTT). *)
Require Import HoTT.


(*! Section 4.  We prove here our admissible rules. !*)
Section Translation.

  Context `{Funext}.

  (* Pointed types as Sigmas *)
  Definition BuildPType A (a : A) : { typ : Type & typ }.
    exists A. exact a.
  Defined.
  Notation "[ A , a ]" := (BuildPType A a) (at level 0).

  (* We state our parametricity axiom. *)
  Axiom axType : forall p : Type = Type, p = idpath.

  (* And its corolarry. *)
  Lemma typeq : forall A B, ([Type, A] = [Type, B]) ->
                       A = B.
  Proof.
    intros A B p.
    pose proof (equiv_path_sigma _ [Type,A] [Type,B]) as h.
    pose proof (h ^-1 p) as h'. simpl in h'.
    destruct h' as [p1 p2].
    rewrite (axType p1) in p2. simpl in p2. exact p2.
  Qed.

  Lemma HSubst : forall A B (p : A = B) (t : A),
                   ([A, t] = [B, p # t]).
  Proof.
    intros A B p t.
    simple refine (path_sigma _ _ _ _ _) ; simpl.
    - exact p.
    - reflexivity.
  Qed.

  Lemma HProd : forall A A' B B'
                  (p : [Type, A] = [Type, A'])
                  (q : forall (x : A) (y : A') (e : [A, x] = [A', y]),
                         [Type, (B x)] = [Type, (B' y)]),
                  [Type, (forall x:A, B x)] = [Type, (forall y:A', B' y)].
  Proof.
    intros A A' B B' p q.
    assert (e : (forall x : A, B x) = (forall y : A', B' y)).
    { cut (A = A').
      - intro h. destruct h.
        cut (forall x:A, B x = B' x).
        + intro h. pose proof (path_forall B B' h) as h'. destruct h'.
          reflexivity.
        + intro x. assert (e : [A, x] = [A, x]) by reflexivity.
          pose proof (q x x e) as h. apply typeq. apply h.
      - apply typeq. apply p.
    }
    simple refine (path_sigma _ _ _ _ _).
    - exact idpath.
    - simpl. exact e.
  Qed.

End Translation.

