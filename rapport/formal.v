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

  Definition forall_eq {A} {B1} {B2} (p : forall x : A, B1 x = B2 x) :
    (forall x : A, B1 x) = (forall x : A, B2 x).
  Proof.
    cut (B1 = B2).
    - intro e. destruct e. exact idpath.
    - apply path_forall. exact p.
  Defined.
  
  Lemma forall_eq_transport :
    forall A B1 B2 (p : forall (x:A), B1 x = B2 x) (t1 : forall (x : A), B1 x),
      @paths (forall (x:A), B2 x)
        (transport idmap (@forall_eq A B1 B2 p) (fun (x : A) => t1 x))
        (fun (x : A) => transport idmap (p x) (t1 x)).
  Proof.
    intros A B1 B2 p t1.
    (* Maybe through univalence? *)
  Abort.

  Lemma HLam : forall A1 A2 B1 B2 t1 t2,
                 [Type, A1] = [Type, A2] ->
                 (forall (x : A1) (y : A2) (p : [A1,x] = [A2,y]),
                    [B1 x, t1 x] = [B2 y, t2 y]) ->
                 [forall (x : A1), B1 x, fun (x:A1) => t1 x] =
                 [forall (y : A2), B2 y, fun (y:A2) => t2 y].
  Proof.
    intros A1 A2 B1 B2 t1 t2 p h.
    assert (e : A1 = A2).
    { apply typeq. exact p. }
    destruct e. rename A1 into A.
    assert (eq : forall x : A, [A, x] = [A, x]) by (intro x ; exact idpath).
    simple refine (path_sigma _ _ _ _ _) ; simpl.
    - exact (forall_eq (fun x => (h x x (eq x))..1)).
    - 

End Translation.

