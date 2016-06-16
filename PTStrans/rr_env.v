(** * Typing Environment Definition and Function Manipulation. *)
Require Import base f_term f_env f_typ rr_term.
Require Import List.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt Le Gt Plus.

Module Type rr_env_mod (X: term_sig) (Y : pts_sig X) (FTM: f_term_mod X) (FEM : f_env_mod X FTM)
                       (RE : resizing_env X Y FTM FEM) (TM : rr_term_mod X Y FTM FEM RE).
 Import TM.

 Definition Env := list Term.

 Set Implicit Arguments.

 Inductive item (A:Type) (x:A): list A ->nat->Prop :=
 | item_hd : forall (Γ : list A), item x (cons x Γ) O
 | item_tl : forall (Γ : list A) (n : nat) (y : A), item x Γ n -> item x (cons y Γ) (S n).

 Hint Constructors item.

 Notation " x ↓ n ∈ Γ " := (item x Γ n) (at level 80, no associativity) : RR_scope.

 Lemma fun_item: forall T (A B:T)(Γ:list T)(n:nat), 
                   A ↓ n ∈ Γ -> B ↓ n ∈ Γ -> A = B.
   intros T A B  Γ n;revert T A B Γ. 
   induction n; intros.
   inversion H; inversion H0.
   rewrite <- H2 in H1; injection H1; trivial.
   inversion H; inversion H0; subst.
   injection H5; intros; subst.
   apply IHn with (Γ:=Γ0); trivial.
 Qed.

 Inductive trunc (A:Type) : nat->list A ->list A->Prop :=
 | trunc_O: forall (Γ:list A) , (trunc O Γ Γ)
 | trunc_S: forall (k:nat)(Γ Γ':list A)(x:A), trunc k Γ Γ' 
                                       -> trunc (S k) (cons x Γ) Γ'.

 Hint Constructors trunc.

 Lemma item_trunc: forall (T:Type) (n:nat) (Γ:list T) (t:T), 
                     t ↓ n ∈ Γ -> exists Γ' , trunc (S n) Γ Γ'.
   intros T n; induction n; intros.
   inversion H.
   exists Γ0.
   apply trunc_S; apply trunc_O.
   inversion H; subst.
   destruct (IHn Γ0 t H2).
   exists x.
   apply trunc_S.
   apply H0.
 Qed.

 Lemma trunc_inj : forall n (Γ Δ Δ':Env),trunc n Γ Δ->trunc n Γ Δ'->Δ=Δ'.
   induction n;inversion 1;inversion 1;subst;[reflexivity|eapply IHn;eassumption].
 Qed.

 Lemma trunc_trans : forall m n (Γ Γ1 Γ2:Env), trunc n Γ Γ1->trunc m Γ1 Γ2->trunc (m+n) Γ Γ2.
   induction n;inversion 1;intros;subst;simpl.
   rewrite plus_comm;assumption.
   rewrite plus_comm;simpl;constructor;rewrite plus_comm;eapply IHn;eassumption.
 Qed.

 Inductive ins_in_env (Γ : Env) (d1 : Term) : nat -> Env -> Env -> Prop :=
 | ins_O: ins_in_env Γ d1 O Γ (d1::Γ)
 | ins_S: forall (n : nat) (Δ Δ' : Env) (d : Term), ins_in_env Γ d1 n Δ Δ'
                                             -> ins_in_env Γ d1 (S n) (d::Δ) ((d ↑ 1 # n) :: Δ').

 Hint Constructors ins_in_env.

 Lemma ins_item_ge: forall (d':Term) (n:nat) (Γ Δ Δ':Env), 
                      ins_in_env Γ d' n Δ Δ' -> 
                      forall (v:nat), n<=v -> 
                      forall (d:Term),  d ↓ v ∈ Δ  -> d ↓ (S v) ∈ Δ'.
   induction n; intros.
   inversion H; subst.
   apply item_tl. exact H1.
   inversion H; subst.
   apply item_tl.
   destruct v.
   elim (le_Sn_O n H0).
   apply IHn with (Γ:=Γ) (Δ:=Δ0).
   trivial.
   apply le_S_n ; trivial.
   inversion H1.
   exact H4.
 Qed.

 Lemma ins_item_lt: forall (d':Term)(n:nat)(Γ Δ Δ':Env),
                      ins_in_env Γ d' n Δ Δ' ->
                      forall (v:nat), n > v ->
                      forall (d:Term), d ↓ v ∈ Δ -> (d ↑ 1 # (n-S v)) ↓ v ∈ Δ' .
   induction n; intros.
   inversion H0.
   inversion H; subst.
   destruct v.
   inversion H1; subst.
   replace (S n -1) with n by intuition.
   apply item_hd.
   apply item_tl.
   replace (S n - S (S v)) with (n -S v) by intuition.
   apply IHn with (Γ:=Γ) (Δ:=Δ0).
   exact H3.
   intuition.
   inversion H1.
   exact H4.
 Qed.

 Lemma ins_item : forall Δ A v Γ Γ', ins_in_env Δ A v Γ Γ' -> A ↓ v ∈ Γ'.
   induction v;inversion 1;subst;constructor;eapply IHv;eassumption.
 Qed.

 Lemma ins_trunc : forall v Δ A Γ Γ',ins_in_env Δ A v Γ Γ'->trunc (S v) Γ' Δ.
   induction v;inversion 1;subst;econstructor;try econstructor;eapply IHv;eassumption.
 Qed.

 Definition item_lift (t:Term) (Γ:Env) (n:nat) :=
   exists u, t = u ↑ (S n) /\  u ↓ n ∈ Γ .

 Hint Unfold item_lift.
 Notation " t ↓ n ⊂ Γ " := (item_lift t Γ n) (at level 80, no associativity): RR_scope.

 (** Properties of the item_lift notation.*)
 Lemma ins_item_lift_lt: forall (d' : Term) (n : nat) (Γ Δ Δ' : Env),
                           ins_in_env Γ d' n Δ Δ' ->
                           forall (v : nat), n > v ->
                             forall (t : Term), t ↓ v ⊂ Δ -> (t ↑ 1 # n) ↓ v ⊂ Δ'.
   intros.
   destruct H1 as [u [ P Q]].
   rewrite P.
   exists (u ↑ 1 # (n - S v) ); split.
   replace n with ( S v + (n -  S v))  by intuition .
   destruct liftP2 as (HH&HH0);rewrite HH.
   replace (S v+(n-S v)-S v) with (n-S v) by intuition.
   reflexivity.
   intuition.
   clear t P.
   inversion H; subst.
   inversion H0.
   inversion Q; subst.
   replace (S n0 -1) with n0 by intuition.
   apply item_hd.
   apply item_tl.
   replace (S n0 - S (S n)) with (n0 -S n) by intuition.
   apply ins_item_lt with d' Γ Δ0; trivial.
   intuition.
 Qed.

 Inductive sub_in_env (Γ : Env) (t T : Term) : nat -> Env -> Env -> Prop :=
 | sub_O :  sub_in_env Γ t T 0 (T :: Γ) Γ
 | sub_S :
     forall Δ Δ' n  B,
       sub_in_env Γ t T n Δ Δ' ->
       sub_in_env Γ t T (S n) (B :: Δ) (B [n← t]  :: Δ').

 Hint Constructors sub_in_env.

 Lemma nth_sub_sup :
   forall n Γ Δ Δ' t T,
     sub_in_env Γ t T n Δ Δ' ->
     forall v : nat, n <= v -> 
              forall d , d ↓ (S v) ∈ Δ -> d ↓ v ∈ Δ'.
   intros n Γ Δ Δ' t T H; induction H; intros.
   inversion H0; subst. trivial.
   inversion H1; subst.
   destruct v.
   elim (le_Sn_O n H0).
   apply item_tl.
   apply le_S_n in H0.
   apply IHsub_in_env; trivial.
 Qed.

 Lemma nth_sub_inf :
   forall t T n Γ Δ Δ',
     sub_in_env Γ t T n Δ Δ' ->
     forall v : nat,
       n > v ->
       forall d , d ↓ v ∈ Δ ->  ( d [n - S v ← t] )↓ v ∈ Δ' .
   intros t T n Γ Δ Δ' H; induction H; intros.
   inversion H.
   destruct v.
   inversion H1; subst.
   replace (S n -1) with n by intuition.
   apply item_hd.
   replace (S n - S (S v)) with (n - S v) by intuition.
   inversion H1; subst.
   apply item_tl.
   apply gt_S_n in H0.
   apply IHsub_in_env; trivial.
 Qed.

 Lemma nth_sub_item_inf :
   forall t T n g e f , sub_in_env g t T n e f ->
                   forall v : nat, n > v ->
                            forall u , item_lift u e v -> item_lift (subst_rec t u n) f v.
   intros.
   destruct H1 as [y [K L]].
   exists (subst_rec t y (n-S v)); split.
   rewrite K; clear u K.
   pattern n at 1 .
   replace n with (S v + ( n - S v)) by intuition.
   apply substP2; intuition.
   apply nth_sub_inf with T g e; trivial.
 Qed.

 Lemma subst_item : forall n Δ T A Γ1 Γ2,sub_in_env Δ T A n Γ1 Γ2->A ↓ n ∈ Γ1.
   induction 1;constructor;assumption.
 Qed.

 Lemma subst_trunc : forall n Δ T A Γ1 Γ2,sub_in_env Δ T A n Γ1 Γ2->trunc (S n) Γ1 Δ.
   induction 1;constructor;constructor||assumption.
 Qed.

 Lemma subst_trunc2 : forall n Δ T A Γ1 Γ2,sub_in_env Δ T A n Γ1 Γ2->trunc n Γ2 Δ.
   induction 1;constructor;constructor||assumption.
 Qed.

 (* We can also lift the inclusion for types to environments. *)
 Definition inrrenv (Γ : FEM.Env) : Env :=
   map inrrt Γ.
 Notation "⟦ Γ ⟧γ" := (inrrenv Γ) (at level 7, no associativity) : RR_scope.

End rr_env_mod.





