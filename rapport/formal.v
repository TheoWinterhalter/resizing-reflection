(* You need to compile it with HoTT (from the github HoTT/HoTT). *)
Require Import HoTT.


(*! Section 4.  We prove here our admissible rules. !*)
Section Translation.

  Context `{Funext}.

  (* Pointed types are records:
     Record pType :=
     { pointed_type : Type ;
       ispointed_type : IsPointed pointed_type }.
     Build_pType is too long a name so we will make a shortcut.
  *)
  Notation "[ A , a ]" := (Build_pType A a) (at level 0).

  (* We state our parametricity axiom. *)
  Axiom axType : forall p : Type = Type, p = idpath.

  (* And its corolarry. *)
  Lemma typeq : forall A B, ([Type, A] = [Type, B]) ->
                       A = B.
  Proof.
    intros A B p.
  Admitted.

  Lemma HSubst : forall A B (p : A = B) (t : A),
                   ([A, t] = [B, transport idmap p t]).
  Proof.
    intros A B p t.
  Admitted.

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
    (* simple refine (path_sigma _ _ _ _ _). *)
Admitted.

End Translation.

