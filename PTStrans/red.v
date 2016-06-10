(** * Beta reduction for annotated terms 
As for the usual terms, we extend the definition of [Beta] to handle the
two additional annotations. Since we want to prove that the typed version
of the reduction is confluent, we don't care to prove it for this version.*)
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt.
Require Import Le.
Require Import Gt.
Require Import Plus.
Require Import Minus.
Require Import Bool.
Require Import base.
Require Import term.

Module Type red_mod (X:term_sig) (TM:term_mod X).
Import TM.
Reserved Notation " A → B " (at level 80).

Inductive Beta : Term -> Term -> Prop :=
 | Beta_head : forall A M N K L , (λ[ A ], M)·(K,L) N → M [← N]
 | Beta_red1 : forall M M' N A B, M → M' -> M·(A,B) N  → M'·(A,B) N
 | Beta_red2 : forall M N N' A B, N → N' -> M·(A,B) N  → M ·(A,B) N'
 | Beta_red3 : forall M N A B B', B → B' -> M·(A,B) N  → M ·(A,B') N
 | Beta_red4 : forall M N A A' B, A → A' -> M·(A,B) N  → M ·(A',B) N
 | Beta_lam  : forall A M M'    , M → M' -> λ[A],M     → λ[A ],M'
 | Beta_lam2 : forall A A' M    , A → A' -> λ[A],M     → λ[A'],M
 | Beta_pi   : forall A B B'    , B → B' -> Π(A),B     → Π(A ),B'
 | Beta_pi2  : forall A A' B    , A → A' -> Π(A),B     → Π(A'),B
 | Beta_id    : forall A A' u  v          , A → A' -> Id A u v      → Id A' u  v
 | Beta_id2   : forall A u  u' v          , u → u' -> Id A u v      → Id A  u' v
 | Beta_id3   : forall A u  v  v'         , v → v' -> Id A u v      → Id A  u  v'
 | Beta_refl  : forall A A' u             , A → A' -> refl A u      → refl A' u
 | Beta_refl2 : forall A u  u'            , u → u' -> refl A u      → refl A  u'
 | Beta_j     : forall A A' C  b  u  v  p  t, A → A' -> J t A C b u v p → J t A' C  b  u  v  p
 | Beta_j2    : forall A C  C' b  u  v  p  t, C → C' -> J t A C b u v p → J t A  C' b  u  v  p
 | Beta_j3    : forall A C  b  b' u  v  p  t, b → b' -> J t A C b u v p → J t A  C  b' u  v  p
 | Beta_j4    : forall A C  b  u  u' v  p  t, u → u' -> J t A C b u v p → J t A  C  b  u' v  p
 | Beta_j5    : forall A C  b  u  v  v' p  t, v → v' -> J t A C b u v p → J t A  C  b  u  v' p
 | Beta_j6    : forall A C  b  u  v  p  p' t, p → p' -> J t A C b u v p → J t A  C  b  u  v  p'
 | Beta_jred  : forall A B  C  b  u  v  w  t,
                  J t A C b u v (refl B w) →
                  b ·(A,(C ↑ 1) ·(A,Π(A ↑ 1), Π(Id (A ↑ 2) #1 #0), !t) #0 ·(A ↑ 1, Π(Id (A ↑ 2) #1 #0), !t) #0 ·(Id (A ↑ 2) #1 #0, !t) (refl (A ↑ 1) #0)) u
where "M → N" := (Beta M N) : Typ_scope.

Reserved Notation " A →→ B" (at level 80).

Inductive Betas : Term -> Term -> Prop :=
 | Betas_refl  : forall M    , M →→ M
 | Betas_Beta  : forall M N  , M → N  -> M →→ N
 | Betas_trans : forall M N P, M →→ N -> N →→ P -> M →→ P
where "A →→ B" := (Betas A B) : Typ_scope.

Hint Constructors Beta Betas.

Lemma Betas_App : forall M M' N N' A A' B B', M →→ M' -> N →→ N' ->  A →→ A' -> B →→ B' -> 
  M·(A,B)N →→ M'·(A',B')N'.
assert (forall a b c A B , b →→ c ->  a·(A,B)b →→ a·(A,B)c).
induction 1; eauto. 
assert (forall a b c A B, b→→c -> b·(A,B) a →→ c·(A,B) a).
induction 1; eauto.
assert (forall a b A B B', B →→ B' -> a·(A,B) b →→ a·(A,B') b).
induction 1; eauto.
assert (forall a b A A' B, A →→ A' -> a·(A,B) b →→ a·(A',B) b).
induction 1; eauto.
intros. eapply Betas_trans. apply H. apply H4. eapply Betas_trans. apply H0. apply H3. eauto.
Qed.

Hint Resolve Betas_App.

Lemma Betas_La : forall A A' M M', A →→ A' -> M →→ M' -> λ[A],M →→ λ[A'],M'.
assert (forall a b c , a →→ b -> λ[c],  a →→ λ[c], b).
induction 1; eauto.
assert (forall a b c, a →→ b -> λ[a], c →→ λ[b], c).
induction 1; eauto.
eauto.
Qed.


Hint Resolve Betas_La.


Lemma Betas_Pi : forall A A' B B', A →→ A' -> B →→ B' -> Π(A),B →→ Π(A'),B'.
assert (forall a b c , a →→ b -> Π (c), a →→ Π(c), b).
induction 1; eauto.
assert (forall a b c, a →→ b -> Π(a), c →→ Π(b), c).
induction 1; eauto.
eauto.
Qed.

Hint Resolve Betas_Pi.

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

Lemma Betas_refls : forall A A' u u', A →→ A' -> u →→ u' -> refl A u →→ refl A' u'.
  assert (forall a b c, a →→ b -> refl c a →→ refl c b).
  { induction 1 ; eauto. }
  assert (forall a b c, a →→ b -> refl a c →→ refl b c).
  { induction 1 ; eauto. }
  eauto.
Qed.

Hint Resolve Betas_refls.

Lemma Betas_J : forall A A' C C' b b' u u' v v' p p' t,
                  A →→ A' -> C →→ C' -> b →→ b' -> u →→ u' -> v →→ v' -> p →→ p' ->
                  J t A C b u v p →→ J t A' C' b' u' v' p'.
  assert (forall a b c d e f g t, a →→ b -> J t c d e f g a →→ J t c d e f g b).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g t, a →→ b -> J t c d e f a g →→ J t c d e f b g).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g t, a →→ b -> J t c d e a f g →→ J t c d e b f g).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g t, a →→ b -> J t c d a e f g →→ J t c d b e f g).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g t, a →→ b -> J t c a d e f g →→ J t c b d e f g).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g t, a →→ b -> J t a c d e f g →→ J t b c d e f g).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g h t, a →→ b -> c →→ d -> J t a c e f g h →→ J t b d e f g h).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g h i t, a →→ b -> c →→ d -> e →→ f -> J t a c e g h i →→ J t b d f g h i).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g h i j t, a →→ b -> c →→ d -> e →→ f -> g →→ h -> J t a c e g i j →→ J t b d f h i j).
  { induction 1 ; eauto. }
  assert (forall a b c d e f g h i j k t, a →→ b -> c →→ d -> e →→ f -> g →→ h -> i →→ j -> J t a c e g i k →→ J t b d f h j k).
  { induction 1 ; eauto. }
  eauto.
Qed.

Hint Resolve Betas_J.

Reserved Notation "M →' N" (at level 80).

Inductive Betap : Term -> Term -> Prop :=
 | Betap_sort : forall s                  , !s →' !s
 | Betap_var  : forall v                  , #v →' #v
 | Betap_lam  : forall A A' M M'          , A →' A' -> M →' M' -> λ[A],M →' λ[A'],M'
 | Betap_pi   : forall A A' B B'          , A →' A' -> B →' B' -> Π(A),B →' Π(A'),B'
 | Betap_App  : forall M M' N N' A A' B B', M →' M' -> N →' N' -> A →' A' -> B →' B' ->
    M ·(A,B) N →' M'·(A',B') N'
 | Betap_head : forall A M M' N N' K L    , M →' M' -> N →' N' -> (λ[A],M)·(K,L) N →' M'[← N']
 | Betap_id   : forall A A' M M' N  N'                 , A →' A' -> M →' M' -> N →' N' -> Id A M N →' Id A' M' N'
 | Betap_rfl  : forall A A' M M'                       , A →' A' -> M →' M' -> refl A M →' refl A' M'
 | Betap_j    : forall A A' C C' b b' u  u' v v' p p' t, A →' A' -> C →' C' -> b →' b' -> u →' u' -> v →' v' -> p →' p' ->
                                                    J t A C b u v p →' J t A' C' b' u' v' p'
 | Betap_jred : forall A A' C C' B b  b' u  u' v  w t  , A →' A' -> C →' C' -> b →' b' -> u →' u' ->
                                                    J t A C b u v (refl B w) →' b' ·(A',(C' ↑ 1) ·(A',Π(A' ↑ 1), Π(Id (A' ↑ 2) #1 #0), !t) #0 ·(A' ↑ 1, Π(Id (A' ↑ 2) #1 #0), !t) #0 ·(Id (A' ↑ 2) #1 #0, !t) (refl (A' ↑ 1) #0)) u'
where "A →' B" := (Betap A B ) : Typ_scope.

Reserved Notation "M  →→' N" (at level 80).

Inductive Betaps : Term -> Term -> Prop :=
 | Betaps_intro : forall M N  , M →'  N -> M →→' N
 | Betaps_trans : forall M N P, M →→' N -> N →→' P -> M →→' P
where "M →→' N" := (Betaps M N) : Typ_scope.


Hint Constructors Betap Betaps. 

Lemma Betap_to_Betas : forall M N, M →' N -> M →→ N.
  induction 1; intuition.
  - eapply Betas_trans. eapply Betas_App. eapply Betas_La. apply Betas_refl.
    apply IHBetap1. apply IHBetap2. apply Betas_refl. apply Betas_refl.
    constructor. econstructor.
  - eapply Betas_trans.
    + eapply Betas_J ; eauto.
    + eauto.
Qed.

Lemma Betaps_to_Betas : forall M N, M →→' N -> M →→ N.
  induction 1; eauto. apply Betap_to_Betas in H; trivial.
Qed.

Lemma Betap_refl : forall M, M →' M.
  induction M; intuition.
Qed.

Hint Resolve Betap_refl.

Lemma Betaps_Beta_closure : forall M N,  M → N -> M →' N.
  induction 1; intuition.
Qed.

Lemma Betaps_Betas_closure :  forall M N, M →→ N -> M →→' N.
  induction 1. intuition.
  apply Betaps_Beta_closure in  H; intuition.
  eauto.
Qed.

End red_mod.
