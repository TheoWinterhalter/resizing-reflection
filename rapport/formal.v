(* You need to compile it with HoTT (from the github HoTT/HoTT). *)
Require Import HoTT.

(*! Section 1. Operations on equality !*)
(* We implement them although they are already available in the HoTT library for
   the sake of the example. *)
Section Operations.

  (* Transport *)
  Definition ex_transport {A} {B} (p : A = B) : A -> B :=
    paths_rect _ A (fun B p => A -> B) (fun x => x) B p.

  (* Ap(plication) *)
  Definition ex_ap {A} {B} (f : A -> B) {x y : A} (p : x = y) : f x = f y :=
    paths_rect A x (fun y p => f x = f y) idpath y p.

  (* Symmetry *)
  Definition ex_sym {A} {x y : A} (p : x = y) : y = x :=
    paths_rect A x (fun y p => y = x) idpath y p.

  (* Transitivity *)
  Definition ex_trans {A} {x y z : A} (p : x = y) (q : y = z) : x = z :=
    paths_rect A x (fun y p => y = z -> x = z) (fun q => q) y p q.

  (* We also explicit the arrow between equality and equivalence. *)
  Definition ex_eq_equiv {A} {B} (p : A = B) : A <~> B.
    simple refine (BuildEquiv A B _ _).
    - exact (transport idmap p).
    - simple refine (BuildIsEquiv A B _ _ _ _ _).
      + exact (transport idmap (p^)).
      + intro x. destruct p. cbn. reflexivity.
      + intro x. destruct p. cbn. reflexivity.
      + intro x. cbn. destruct p. cbn. reflexivity.
  Qed.

End Operations.

(*! Section 3. Reduction between rules. !*)
Section OneRule.

  (* Propositions are embedded in True *)
  Lemma prop_in_top :
    forall (A : Type) `{h : IsHProp A}, { f : A -> True | IsEmbedding f}.
  Proof.
    intros A h.
    exists (fun a => tt). intro x. destruct x.
    
    intros x y. destruct x as [x p]. destruct y as [y q].
    assert (e : x = y).
    - apply path_ishprop.
    - destruct e. assert (e : p = q).
      + apply hset_decpaths. intros u v. destruct u. destruct v.
        left. reflexivity.
      + destruct e. exists idpath. intro y.
        apply hset_decpaths. intros u v.
        destruct u as [u q]. destruct v as [v r].
        assert (e : u = v).
        * apply path_ishprop.
        * { destruct e. assert (e : q = r).
            - apply hset_decpaths. intros v w.
              destruct v. destruct w. left. reflexivity.
            - destruct e. left. exact idpath.
          }
  Qed.

End OneRule.

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
    intros A B1 B2 p t1. cbn.
    apply path_forall; intro x. unfold forall_eq. cbn.

    path_via (transport idmap ((apD10 (path_forall B1 B2 p)) x) (t1 x)).
    - generalize (path_forall B1 B2 p). intro q; destruct q.
      reflexivity.
    - rewrite apD10_path_forall. reflexivity.
  Defined.

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
    - eapply transitivity.
      + apply forall_eq_transport.
      + cbn. apply path_forall. intro x.
        exact ((h x x (eq x))..2).
  Qed.

End Translation.

