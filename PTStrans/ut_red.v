(** * Beta-reduction definition and properties.*)
Require Import base ut_term.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt Plus.


Module Type ut_red_mod (X:term_sig)  (TM : ut_term_mod X).
 Import TM.

(** ** Usual Beta-reduction:
 - one step
 - multi step (reflexive, transitive closure)
 - converesion (reflexive, symetric, transitive closure)
 *)
Reserved Notation " A → B " (at level 80).

Inductive Beta : Term -> Term -> Prop :=
| Beta_head  : forall A M  N             , (λ[A], M)· N → M [← N]
| Beta_red1  : forall M M' N             , M → M' -> M · N         → M'· N
| Beta_red2  : forall M N  N'            , N → N' -> M · N         → M · N'
| Beta_lam   : forall A M  M'            , M → M' -> λ[A],M        → λ[A ],M'
| Beta_lam2  : forall A A' M             , A → A' -> λ[A],M        → λ[A'],M
| Beta_pi    : forall A B  B'            , B → B' -> Π(A),B        → Π(A ),B'
| Beta_pi2   : forall A A' B             , A → A' -> Π(A),B        → Π(A'),B
| Beta_id    : forall A A' u  v          , A → A' -> Id A u v      → Id A' u  v
| Beta_id2   : forall A u  u' v          , u → u' -> Id A u v      → Id A  u' v
| Beta_id3   : forall A u  v  v'         , v → v' -> Id A u v      → Id A  u  v'
| Beta_refl  : forall A A' u             , A → A' -> refl A u      → refl A' u
| Beta_refl2 : forall A u  u'            , u → u' -> refl A u      → refl A  u'
| Beta_j     : forall A A' C  b  u  v  p , A → A' -> J A C b u v p → J A' C  b  u  v  p
| Beta_j2    : forall A C  C' b  u  v  p , C → C' -> J A C b u v p → J A  C' b  u  v  p
| Beta_j3    : forall A C  b  b' u  v  p , b → b' -> J A C b u v p → J A  C  b' u  v  p
| Beta_j4    : forall A C  b  u  u' v  p , u → u' -> J A C b u v p → J A  C  b  u' v  p
| Beta_j5    : forall A C  b  u  v  v' p , v → v' -> J A C b u v p → J A  C  b  u  v' p
| Beta_j6    : forall A C  b  u  v  p  p', p → p' -> J A C b u v p → J A  C  b  u  v  p'
| Beta_jred  : forall A B  C  b  u  v  w , J A C b u v (refl B w) → b · u
where "M → N" := (Beta M N) : UT_scope.

Reserved Notation " A →→ B " (at level 80).

Inductive Betas : Term -> Term -> Prop :=
 | Betas_refl  : forall M    , M →→ M
 | Betas_Beta  : forall M N  , M → N  -> M →→ N
 | Betas_trans : forall M N P, M →→ N -> N →→ P -> M →→ P
where  " A →→ B " := (Betas A B) : UT_scope.

Reserved Notation " A ≡ B " (at level 80).

Inductive Betac : Term -> Term -> Prop :=
 | Betac_Betas : forall M N  , M →→ N -> M ≡ N
 | Betac_sym   : forall M N  , M ≡ N  -> N ≡ M
 | Betac_trans : forall M N P, M ≡ N  -> N ≡ P -> M ≡ P
where " A ≡ B " := (Betac A B)  : UT_scope.

Hint Constructors Beta.
Hint Constructors Betas.
Hint Constructors Betac.

(** Facts about [Betas] and [Betac]: Congruence. *)
Lemma Betac_refl : forall M, M ≡ M.
intros; constructor; constructor.
Qed.

Hint Resolve Betac_refl.

Lemma Betas_App : forall M M' N N',M →→ M' -> N →→ N' -> M · N →→ M' · N'.
assert (forall a b c, b →→ c ->  a·b →→ a·c).
induction 1; eauto.
assert (forall a b c, b→→c -> b· a →→ c· a).
induction 1; eauto.
intros; eauto.
Qed.

Hint Resolve Betas_App.

Lemma Betac_App : forall M M' N N' , M ≡ M' -> N ≡ N' -> M · N ≡ M' · N'.
assert (forall a b c, b ≡ c ->  a· b ≡ a· c).
induction 1; eauto.
assert (forall a b c , b ≡ c -> b·a ≡ c·a).
induction 1; eauto.
eauto.
Qed.

Hint Resolve Betac_App.

Lemma Betas_La : forall A A' M M', A →→ A' -> M →→ M' -> λ[A],M →→ λ[A'],M'.
assert (forall a b c , a →→ b -> λ[c],  a →→ λ[c], b).
induction 1; eauto.
assert (forall a b c, a →→ b -> λ[a], c →→ λ[b], c).
induction 1; eauto.
eauto.
Qed.


Hint Resolve Betas_La.

Lemma Betac_La: forall A A' M M', A ≡ A' -> M ≡ M' -> λ[A],M ≡ λ[A'],M'.
assert (forall a b c, a ≡ b -> λ[c], a ≡ λ[c], b).
induction 1; eauto.
assert (forall a b c, a ≡ b -> λ[a], c ≡ λ[b], c).
induction 1; eauto.
eauto.
Qed.

Hint Resolve Betac_La.

Lemma Betas_Pi : forall A A' B B', A →→ A' -> B →→ B' -> Π(A),B →→ Π(A'),B'.
assert (forall a b c , a →→ b -> Π (c), a →→ Π(c), b).
induction 1; eauto.
assert (forall a b c, a →→ b -> Π(a), c →→ Π(b), c).
induction 1; eauto.
eauto.
Qed.

Hint Resolve Betas_Pi.

Lemma Betac_Pi : forall A A' B B', A ≡ A' -> B ≡ B' -> Π(A),B ≡ Π(A'),B'.
assert (forall a b c , a ≡ b -> Π(c), a ≡ Π(c), b).
induction 1; eauto.
assert (forall a b c, a ≡ b -> Π(a), c ≡ Π(b), c).
induction 1; eauto.
eauto.
Qed.

Hint Resolve Betac_Pi.

Lemma Betas_Id : forall A A' u u' v v', A →→ A' -> u →→ u' -> v →→ v' -> Id A u v →→ Id A' u' v'.
  assert (forall a b c d, a →→ b -> Id c d a →→ Id c d b).
  { induction 1 ; eauto. }
  assert (forall a b c d, a →→ b -> Id c a d →→ Id c b d).
  { induction 1 ; eauto. }
  assert (forall a b c d, a →→ b -> Id a c d →→ Id b c d).
  { induction 1 ; eauto. }
  assert (forall A A' u u' v, A →→ A' -> u →→ u' -> Id A u v →→ Id A' u' v).
  { induction 1 ; eauto. }
  eauto.
Qed.

Hint Resolve Betas_Id.

Lemma Betac_Id : forall A A' u u' v v', A ≡ A' -> u ≡ u' -> v ≡ v' -> Id A u v ≡ Id A' u' v'.
  assert (forall a b c d, a ≡ b -> Id c d a ≡ Id c d b).
  { induction 1 ; eauto. }
  assert (forall a b c d, a ≡ b -> Id c a d ≡ Id c b d).
  { induction 1 ; eauto. }
  assert (forall a b c d, a ≡ b -> Id a c d ≡ Id b c d).
  { induction 1 ; eauto. }
  assert (forall A A' u u' v, A ≡ A' -> u ≡ u' -> Id A u v ≡ Id A' u' v).
  { induction 1 ; eauto. }
  eauto.
Qed.

Hint Resolve Betac_Id.

Lemma Betas_refls : forall A A' u u', A →→ A' -> u →→ u' -> refl A u →→ refl A' u'.
  assert (forall a b c, a →→ b -> refl c a →→ refl c b).
  { induction 1 ; eauto. }
  assert (forall a b c, a →→ b -> refl a c →→ refl b c).
  { induction 1 ; eauto. }
  eauto.
Qed.

Hint Resolve Betas_refls.

Lemma Betac_refls : forall A A' u u', A ≡ A' -> u ≡ u' -> refl A u ≡ refl A' u'.
  assert (forall a b c, a ≡ b -> refl c a ≡ refl c b).
  { induction 1 ; eauto. }
  assert (forall a b c, a ≡ b -> refl a c ≡ refl b c).
  { induction 1 ; eauto. }
  eauto.
Qed.

Hint Resolve Betac_refls.

Lemma Betas_J : forall A A' C C' b b' u u' v v' p p',
                  A →→ A' -> C →→ C' -> b →→ b' -> u →→ u' -> v →→ v' -> p →→ p' ->
                  J A C b u v p →→ J A' C' b' u' v' p'.
  assert (forall a b c d e f g, a →→ b -> J c d e f g a →→ J c d e f g b).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g, a →→ b -> J c d e f a g →→ J c d e f b g).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g, a →→ b -> J c d e a f g →→ J c d e b f g).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g, a →→ b -> J c d a e f g →→ J c d b e f g).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g, a →→ b -> J c a d e f g →→ J c b d e f g).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g, a →→ b -> J a c d e f g →→ J b c d e f g).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g h, a →→ b -> c →→ d -> J a c e f g h →→ J b d e f g h).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g h i, a →→ b -> c →→ d -> e →→ f -> J a c e g h i →→ J b d f g h i).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g h i j, a →→ b -> c →→ d -> e →→ f -> g →→ h -> J a c e g i j →→ J b d f h i j).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g h i j k, a →→ b -> c →→ d -> e →→ f -> g →→ h -> i →→ j -> J a c e g i k →→ J b d f h j k).
  { induction 1 ; eauto. }
  eauto.
Qed.

Hint Resolve Betas_J.

Lemma Betac_J : forall A A' C C' b b' u u' v v' p p',
                  A ≡ A' -> C ≡ C' -> b ≡ b' -> u ≡ u' -> v ≡ v' -> p ≡ p' ->
                  J A C b u v p ≡ J A' C' b' u' v' p'.
  assert (forall a b c d e f g, a ≡ b -> J c d e f g a ≡ J c d e f g b).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g, a ≡ b -> J c d e f a g ≡ J c d e f b g).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g, a ≡ b -> J c d e a f g ≡ J c d e b f g).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g, a ≡ b -> J c d a e f g ≡ J c d b e f g).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g, a ≡ b -> J c a d e f g ≡ J c b d e f g).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g, a ≡ b -> J a c d e f g ≡ J b c d e f g).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g h, a ≡ b -> c ≡ d -> J a c e f g h ≡ J b d e f g h).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g h i, a ≡ b -> c ≡ d -> e ≡ f -> J a c e g h i ≡ J b d f g h i).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g h i j, a ≡ b -> c ≡ d -> e ≡ f -> g ≡ h -> J a c e g i j ≡ J b d f h i j).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g h i j k, a ≡ b -> c ≡ d -> e ≡ f -> g ≡ h -> i ≡ j -> J a c e g i k ≡ J b d f h j k).
  { induction 1 ; eauto. }
  eauto.
Qed.

Hint Resolve Betac_J.

Lemma Beta_beta : forall M N P n,  M → N ->  M[n←P] → N[n←P] .
intros.
generalize n.
induction H; intros; simpl; intuition.
rewrite (subst_travers).
replace (n0+1) with (S n0).
constructor.
rewrite plus_comm. trivial.
Qed.

(** Some "inversion" lemmas : 
 - a variable/sort cannot reduce at all
 - a pi/lam can only reduce to another pi/lam
 - ...
*)
Lemma Betas_V : forall x N, #x →→ N -> N = #x.
intros. remember #x as X; induction H; trivial.
subst; inversion H.
transitivity N. apply IHBetas2. rewrite <- HeqX; intuition. intuition.
Qed.


Lemma Betas_S : forall s N, !s →→ N -> N = !s.
intros. remember !s as S; induction H; trivial.
subst; inversion H.
transitivity N. apply IHBetas2. rewrite <- HeqS; intuition. intuition.
Qed.


Lemma Betas_Pi_inv : forall A B N, Π(A), B →→ N -> 
  exists C, exists D, N = Π(C), D /\ A →→ C /\ B →→ D.
intros.
remember (Π(A), B) as P. revert A B HeqP; induction H; intros; subst; eauto.
inversion H; subst; clear H.
exists A; exists B'; intuition.
exists A'; exists B; intuition.
destruct (IHBetas1 A B) as (C' & D' & ?); intuition.
destruct (IHBetas2 C' D') as (C'' & D'' &?); intuition.
exists C''; exists D''; eauto.
Qed.

Lemma Betas_Id_inv : forall A u v N, Id A u v →→ N ->
                                exists B, exists w, exists z, N = Id B w z /\ A →→ B /\ u →→ w /\ v →→ z.
  intros A u v N h.
  remember (Id A u v) as P. revert A u v HeqP ; induction h ; intros ; subst ; eauto.
  - exists A ; exists u ; exists v ; intuition.
  - inversion H ; subst ; clear H.
    + exists A' ; exists u  ; exists v  ; intuition.
    + exists A  ; exists u' ; exists v  ; intuition.
    + exists A  ; exists u  ; exists v' ; intuition.
  - destruct (IHh1 A u v) as (B' & u' & v' & ?).
    + reflexivity.
    + destruct (IHh2 B' u' v') as (B'' & u'' & v'' & ?).
      * apply H.
      * exists B'' ; exists u'' ; exists v''.
        repeat split ; try apply H0 ;
        (eapply Betas_trans ; try apply H ; try apply H0).
Qed.
        
(** Lift properties.*)
Lemma Beta_lift: forall M N  n m, M → N -> M ↑ n # m → N ↑ n # m .
intros.
generalize n m; clear n m.
induction H; intros; simpl; eauto.
change m with (0+m).
rewrite substP1.
constructor.
Qed.


Lemma Betas_lift : forall M N n m , M →→ N -> M ↑ n # m →→ N ↑ n # m .
intros.
induction H.
constructor.
constructor; apply Beta_lift; intuition.
apply Betas_trans with (N:= N ↑ n # m ); intuition.
Qed.



Lemma Betac_lift : forall M N n m, M ≡ N -> M ↑ n # m ≡ N ↑ n # m .
intros.
induction H.
constructor.
apply Betas_lift; trivial.
apply Betac_sym; trivial.
apply Betac_trans with (N ↑ n # m); trivial.
Qed.

Hint Resolve Beta_lift Betas_lift Betac_lift.


(** Subst properties.*)
Lemma Betas_subst : forall M P P' n, P →→ P' -> M [n←P] →→ M[n← P']. 
induction M; intros; simpl; eauto.
- destruct (lt_eq_lt_dec v n); intuition.
- apply Betas_J ; eauto.
Qed.

Hint Resolve Betas_subst.

Lemma Betas_subst2 : forall M N P n, M →→ N -> M [n← P] →→ N [n ← P].
induction 1; eauto.
constructor. apply Beta_beta; intuition.
Qed.


Hint Resolve Betas_subst2.

Lemma Betac_subst : forall M P P' n, P ≡ P' -> M[n←P] ≡ M [n←P'].
induction M; simpl; intros; intuition.
destruct (lt_eq_lt_dec v n); intuition.
Qed.

Lemma Betac_subst2 : forall M N P n, 
  M ≡ N -> M[n←P] ≡ N[n← P] .
induction 1; eauto.
Qed.

Hint Resolve Betac_subst Betac_subst2.


(** ** Parallel Reduction
We use the parallel reduction to prove that [Beta] is confluent.*)
Reserved Notation "M →' N" (at level 80).

(** Beta parallel definition. *)
Inductive Betap : Term -> Term -> Prop :=
 | Betap_sort : forall s                               , !s →' !s
 | Betap_var  : forall x                               , #x →' #x
 | Betap_lam  : forall A A' M  M'                      , A →' A' -> M →' M' -> λ[A],M →' λ[A'],M'
 | Betap_pi   : forall A A' B  B'                      , A →' A' -> B →' B' -> Π(A),B →' Π(A'),B'
 | Betap_app  : forall M M' N  N'                      , M →' M' -> N →' N' -> M · N  →' M' · N'
 | Betap_head : forall A M  M' N  N'                   , M →' M' -> N →' N' -> (λ[A],M)· N →' M'[← N']
 | Betap_id   : forall A A' M  M' N  N'                , A →' A' -> M →' M' -> N →' N' -> Id A M N →' Id A' M' N'
 | Betap_rfl  : forall A A' M  M'                      , A →' A' -> M →' M' -> refl A M →' refl A' M'
 | Betap_j    : forall A A' C  C' b  b' u  u' v v' p p', A →' A' -> C →' C' -> b →' b' -> u →' u' -> v →' v' -> p →' p' ->
                                                    J A C b u v p →' J A' C' b' u' v' p'
 | Betap_jred : forall A B  C  b  b' u  u' v  w        , b →' b' -> u →' u' ->
                                                    J A C b u v (refl B w) →' b' · u'
where "M →' N" := (Betap M N) : UT_scope.


Notation "m →' n" := (Betap m n) (at level 80) : UT_scope.

Hint Constructors Betap.

Lemma Betap_refl : forall M, M →' M.
induction M; eauto.
Qed.

Hint Resolve Betap_refl.

(** Lift and Subst property of [Betap].*)
Lemma Betap_lift: forall M N n m, M →' N -> M ↑ n # m →' N ↑ n # m .
intros.
revert n m.
induction H; simpl; intuition.
change m with (0+m).
rewrite substP1.
constructor; intuition.
Qed.

Hint Resolve Betap_lift.

Lemma Betap_subst:forall M M' N N' n, M →' M'  -> N →' N' -> M[n←N] →' M'[n←N'].
intros. revert n.
induction H; simpl; intuition.
destruct lt_eq_lt_dec; intuition.
rewrite subst_travers. replace (S n) with (n+1) by (rewrite plus_comm; trivial). constructor; intuition.
Qed.

Hint Resolve Betap_subst.

(** [Betap] has the diamond property. *)
Lemma Betap_diamond : forall M N P,
   M →' N -> M →' P -> exists Q, N →' Q /\ P →' Q. 
intros.
revert P H0.
induction H; intros.
(**)
exists P; intuition.
(**)
exists P; intuition.
(**)
inversion H1; subst; clear H1.
destruct (IHBetap1 A'0 H4) as (A'' & ? & ?).
destruct (IHBetap2 M'0 H6) as (M'' & ?& ?).
exists (λ[A''],M''); intuition. 
(**)
inversion H1; subst; clear H1.
destruct (IHBetap1 A'0 H4) as (A'' & ? & ?).
destruct (IHBetap2 B'0 H6) as (B'' & ?& ?).
exists (Π(A''), B''); intuition. 
(**)
inversion H1; subst; clear H1.
destruct (IHBetap1 M'0 H4) as (M'' & ?& ?).
destruct (IHBetap2 N'0 H6) as (N'' & ?& ?).
exists (M'' · N''); intuition.
inversion H; subst; clear H.
destruct (IHBetap2 N'0 H6) as (N'' & ?& ?).
destruct (IHBetap1 (λ[A],M'0)) as  (L & ?& ?); intuition.
inversion H2; subst; clear H2; inversion H5; subst; clear H5.
exists ( M' [ ← N'']); intuition.
(**)
inversion H1; subst; clear H1.
destruct (IHBetap2 N'0 H6) as (N'' & ?& ?).
inversion H4; subst; clear H4.
destruct (IHBetap1 M'1 H9) as (M'' & ?& ?).
exists (M''[← N'']); intuition.
destruct (IHBetap2 N'0 H7) as (N'' & ?& ?).
destruct (IHBetap1 M'0 H6) as (M'' & ?& ?).
exists (M''[← N'']); intuition.
(**)
- inversion H2 ; subst ; clear H2.
  destruct (IHBetap3 N'0 H9) as (N'' & ? & ?).
  destruct (IHBetap2 M'0 H8) as (M'' & ? & ?).
  destruct (IHBetap1 A'0 H6) as (A'' & ? & ?).
  exists (Id A'' M'' N''). intuition.
- inversion H1 ; subst ; clear H1.
  destruct (IHBetap1 A'0 H4) as (A'' & ? & ?).
  destruct (IHBetap2 M'0 H6) as (M'' & ? & ?).
  exists (refl A'' M'') ; intuition.
- inversion H5 ; subst ; clear H5.
  + destruct (IHBetap1 A'0 H12) as (A'' & ? & ?).
    destruct (IHBetap2 C'0 H14) as (C'' & ? & ?).
    destruct (IHBetap3 b'0 H15) as (b'' & ? & ?).
    destruct (IHBetap4 u'0 H16) as (u'' & ? & ?).
    destruct (IHBetap5 v'0 H17) as (v'' & ? & ?).
    destruct (IHBetap6 p'0 H18) as (p'' & ? & ?).
    exists (J A'' C'' b'' u'' v'' p'') ; intuition.
  + inversion H4 ; subst ; clear H4.
    destruct (IHBetap3 b'0 H13) as (b'' & ? & ?).
    destruct (IHBetap4 u'0 H14) as (u'' & ? & ?).
    exists (b'' · u'') ; intuition.
- inversion H1 ; subst ; clear H1.
  + inversion H14 ; subst ; clear H14.
    destruct (IHBetap1 b'0 H11) as (b'' & ? & ?).
    destruct (IHBetap2 u'0 H12) as (u'' & ? & ?).
    exists (b'' · u'') ; intuition.
  + destruct (IHBetap1 b'0 H10) as (b'' & ? & ?).
    destruct (IHBetap2 u'0 H11) as (u'' & ? & ?).
    exists (b'' · u'') ; intuition.
Qed.


(** Reflexive Transitive closure of [Betap].*)
Reserved Notation " x  →→' y " (at level 80).

Inductive Betaps : Term -> Term -> Prop :=
 | Betaps_refl  : forall M    , M →→' M
 | Betaps_trans : forall M N P, M  →' N -> N  →→' P -> M  →→' P
where " x  →→' y " := (Betaps x y) : UT_scope.

Hint Constructors Betaps.

(** Closure properties to relate [Betaps] and [Betas].*)
Lemma Betas_Betap_closure : forall M N , M →' N -> M →→ N.
induction 1; eauto.
Qed.

Local Hint Resolve Betas_Betap_closure.


Lemma Betas_Betaps_closure : forall M N,  M →→' N -> M →→  N.
induction 1; eauto.
Qed.

Lemma Betap_Beta_closure : forall M N, M → N -> M →' N.
induction 1; intuition.
Qed.

Local Hint Resolve Betas_Betaps_closure Betap_Beta_closure.

Lemma Betaps_Beta_closure :forall M N, M → N -> M →→' N.
eauto.
Qed.

Local Hint Resolve Betaps_Beta_closure.

Lemma Betaps_trans2 : forall M N P, M →→' N -> N →→' P  -> M →→' P.
intros. revert P H0; induction H; eauto.
Qed.

Local Hint Resolve Betaps_trans2.

Lemma Betaps_Betas_closure : forall M N , M →→ N -> M →→' N.
induction 1; eauto.
Qed.

Local Hint Resolve Betaps_Betas_closure.

(** [Betas] inherites its diamond property from [Betaps].*)
Lemma sub_diamond_Betaps : 
(   forall M N P, M →' N -> M →'  P -> exists Q, N →'  Q /\ P →' Q )
 -> forall M N P, M →' N -> M →→' P -> exists Q, N →→' Q /\ P →' Q .
intros.
revert N H0. induction H1; eauto. 
intros.
destruct (H M N N0 H0 H2) as (Q & ?& ?).
destruct (IHBetaps Q H3) as (Q'' & ? & ?).
exists Q''; eauto.
Qed.



Lemma diamond_Betaps : 
( forall M N P, M →'  N -> M →'  P -> exists Q, N →'  Q /\ P →'  Q)  ->
  forall M N P, M →→' N -> M →→' P -> exists Q, N →→' Q /\ P →→' Q .
intros.  revert P H1.
induction H0; intros; eauto.
destruct (sub_diamond_Betaps H M N P0 H0 H2) as (Q & ? & ?).
destruct (IHBetaps Q H3) as (Q'' & ?& ?). 
exists Q'';eauto.
Qed.


Theorem Betas_diamond: 
  forall M N P, M →→ N -> M →→ P -> exists Q, N →→ Q /\ P →→ Q.
intros.
destruct (diamond_Betaps Betap_diamond M N P) as (Q & ?& ?); intuition.
exists Q; intuition.
Qed.


(** So [Beta] is confluent.*)
Theorem Betac_confl : forall M N, M ≡ N -> exists Q, M →→ Q /\ N →→ Q.
induction 1; eauto. destruct IHBetac as (Q & ? &? ); eauto.
destruct IHBetac1 as (Q1 & ? &? ), IHBetac2 as (Q2 & ? & ?).
destruct (Betas_diamond N Q1 Q2) as (Q'' & ?& ?); trivial.
exists Q''; eauto.
Qed.

(** Some consequences:
 - convertible sorts are equal
 - converitble vars are equal
 - Pi-types are Injective
 - Pi and sorts are not convertible
 - Id-types are injective
 - Id and sorts are not convertible
 *)
Lemma conv_sort : forall s t, !s ≡ !t -> s = t.
intros.
apply Betac_confl in H. destruct H as (z & ?& ?).
apply Betas_S in H.
apply Betas_S in H0.
rewrite H in H0.
injection H0; trivial.
Qed.

Lemma conv_to_sort : forall s T, !s ≡ T ->  T →→ !s.
intros.
apply Betac_confl in H.
destruct H as (z & ?& ?). 
apply Betas_S in H.
subst. trivial.
Qed.

Lemma conv_var : forall x y, #x ≡ #y -> x = y.
intros.
apply Betac_confl in H. destruct H as (z & ?& ?).
apply Betas_V in H. apply Betas_V in H0.
rewrite H in H0.
injection H0; trivial.
Qed.


Lemma conv_to_var : forall x T , #x ≡ T -> T →→ #x.
intros.
apply Betac_confl in H.
destruct H as (z & ?& ?).
apply Betas_V in H.
subst; trivial.
Qed.



(* Pi is injective *)
Theorem PiInj : forall A B C D, Π(A), B ≡ Π(C), D ->  A ≡ C /\ B ≡ D.
intros.
apply Betac_confl in H. destruct H as (z & ? & ?).
apply Betas_Pi_inv in H.
apply Betas_Pi_inv in H0.
destruct H as (c1 & d1 & ? & ? & ?). 
destruct H0 as (c2 & d2 & ? & ?& ?).
rewrite H0 in H; injection H; intros; subst; split; eauto.
Qed.


Lemma Betac_not_Pi_sort : forall A B s, ~ (Π(A), B ≡ !s ).
intros; intro. apply Betac_sym in H. apply conv_to_sort in H.
apply Betas_Pi_inv in H as (C & D & ? & ? & ?). discriminate.
Qed.


(* Id is injective *)
Theorem IdInj : forall A B u v x y, Id A u v ≡ Id B x y -> A ≡ B /\ u ≡ x /\ v ≡ y.
  intros A B u v x y h.
  apply Betac_confl in h. destruct h as [T [hA hB]].
  apply Betas_Id_inv in hA. destruct hA as [A1 [u1 [v1 [hT1 [hA1 [hu1 hv1]]]]]].
  apply Betas_Id_inv in hB. destruct hB as [A2 [u2 [v2 [hT2 [hA2 [hu2 hv2]]]]]].
  rewrite hT2 in hT1. injection hT1. intros eqv equ eqA. subst. repeat split ; eauto.
Qed.

Lemma Betac_not_Id_sort : forall A u v s, ~ (Id A u v ≡ !s).
  intros A u v s bot. apply Betac_sym in bot. apply conv_to_sort in bot.
  apply Betas_Id_inv in bot as (B & w & z & bot & ?). discriminate.
Qed.

End ut_red_mod.
