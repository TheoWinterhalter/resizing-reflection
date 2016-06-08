(** *Typing rules for PTSF.*)
Require Import f_term f_env.
Require Import base.
Require Import List.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt Le Gt Plus Minus.

Module f_typ_mod (X:term_sig) (Y:pts_sig X) (TM: f_term_mod X) (EM: f_env_mod X TM) (*(RM: f_red_mod X TM)*).
  Import X Y TM EM.

(** Typing judgements.

The equivalence of these rules with the alternative rules in the paper 
is proven at the bottom of this file.
*)
Reserved Notation "Γ ⊢ t : T" (at level 80, t, T at level 30, no associativity) .
Reserved Notation "Γ ⊣ " (at level 80, no associativity).
Reserved Notation "Γ ⊢ H : M = N" (at level 80, H, M, N at level 30, no associativity).

Inductive wf : Env -> Prop :=
 | wf_nil  : nil ⊣
 | wf_cons : forall Γ A s, Γ ⊢ A : !s -> A::Γ ⊣
where "Γ ⊣" := (wf Γ) : F_scope
with typ   : Env -> Term -> Term -> Prop :=
 | cSort   : forall Γ s t, Ax s t -> Γ ⊣ -> Γ  ⊢ !s : !t
 | cVar    : forall Γ A v, Γ ⊣ -> A ↓ v  ⊂ Γ -> Γ ⊢ #v : A
 | cProd   : forall Γ A B s1 s2 s3, Rel s1 s2 s3 -> Γ ⊢ A : !s1 -> A::Γ ⊢ B : !s2 -> Γ ⊢  Π(A), B : !s3
 | cAbs    : forall Γ A B b s1 s2 s3, Rel s1 s2 s3 -> Γ ⊢ A : !s1 -> A::Γ ⊢ b : B -> A::Γ ⊢ B : !s2 -> Γ ⊢ λ[A], b : Π(A), B
 | cApp    : forall Γ F a A B , Γ ⊢ F : Π(A), B -> Γ ⊢ a : A -> Γ ⊢ F · a : B[←a]
 | cConv    : forall Γ a A B s H, Γ ⊢ a : A -> Γ ⊢ B : !s -> Γ ⊢ H : A = B -> Γ ⊢ a ∽ H : B
where "Γ ⊢ t : T" := (typ Γ t T) : F_scope
with typ_h : Env -> Prf -> Term -> Term -> Prop :=
 | cRefl   : forall Γ a A, Γ ⊢ a : A -> Γ ⊢ ρ a : a = a
 | cSym    : forall Γ H A B, Γ ⊢ H : A = B -> Γ ⊢ H† : B = A
 | cTrans  : forall Γ H K A B C, Γ ⊢ H : A = B -> Γ ⊢ K : B = C -> Γ ⊢ H•K : A = C
 | cBeta   : forall Γ a A b B s1 s2 s3, Rel s1 s2 s3 -> Γ ⊢ a : A -> Γ ⊢ A : !s1 
                      -> A::Γ ⊢ b : B -> A::Γ ⊢ B : !s2 -> Γ ⊢ β((λ[A], b)·a) : (λ[A], b)·a = b[←a]
 | cProdEq : forall Γ A A' B B' H K s1 s2 s3 s1' s2' s3', Rel s1 s2 s3 -> Rel s1' s2' s3' 
                      -> Γ ⊢ A : !s1 -> Γ ⊢ A' : !s1' -> A::Γ ⊢ B : !s2 -> A'::Γ ⊢ B' : !s2' 
                      -> Γ ⊢ H : A = A' -> A::Γ ⊢ K : B = (B'↑1#1)[←#0∽H↑h1] -> Γ ⊢ {H,[A]K} : Π(A), B = Π(A'), B'
 | cAbsEq  : forall Γ A A' b b' B B' H K s1 s2 s3 s1' s2' s3', Rel s1 s2 s3 -> Rel s1' s2' s3' 
                      -> Γ ⊢ A : !s1 -> Γ ⊢ A' : !s1' -> A::Γ ⊢ b : B -> A'::Γ ⊢ b' : B' -> A::Γ ⊢ B : !s2 -> A'::Γ ⊢ B' : !s2' 
                      -> Γ ⊢ H : A = A' -> A::Γ ⊢ K : b = (b'↑1#1)[←#0∽H↑h1] -> Γ ⊢ ⟨H,[A]K⟩ : λ[A], b = λ[A'], b'
 | cAppEq  : forall Γ F F' a a' A A' B B' H K, Γ ⊢ F : Π(A), B -> Γ ⊢ F' : Π(A'), B' -> Γ ⊢ a : A -> Γ ⊢ a' : A' 
                      -> Γ ⊢ H : F = F' -> Γ ⊢ K : a = a' -> Γ ⊢ H ·h K : F · a = F' · a'
 | cIota    : forall Γ a A B s H, Γ ⊢ a : A -> Γ ⊢ B : !s -> Γ ⊢ H : A = B -> Γ ⊢ ι(a∽H) : a = a∽H
where "Γ ⊢ H : A = B" := (typ_h Γ H A B) : F_scope.

Hint Constructors wf typ typ_h.

Open Scope F_scope.

Scheme typ_ind' := Induction for typ   Sort Prop
 with   wf_ind' := Induction for wf    Sort Prop
 with typh_ind' := Induction for typ_h Sort Prop.

Combined Scheme typ_induc from typ_ind', typh_ind',wf_ind'.


(** some simple rewrite rules, if the statement P is an conjunction*)
Ltac rewrite_l P := rewrite ((and_ind (fun A _ => A)) P).
Ltac rewrite_r P := rewrite ((and_ind (fun _ A => A)) P).
Ltac rewrite_l_rev P := rewrite <- ((and_ind (fun A _ => A)) P).
Ltac rewrite_r_rev P := rewrite <- ((and_ind (fun _ A => A)) P).


Definition semitype A Γ := (exists s,A=!s)\/(exists s, Γ ⊢ A : !s).
Definition has_type A Γ := (exists B, Γ ⊢ A : B).
Definition is_type  A Γ := (exists B, Γ ⊢ B : A).
Definition typ_h_short Γ A B := (exists H, Γ ⊢ H : A = B).
Notation "Γ ⊢ M = N" := (typ_h_short Γ M N) (at level 80, M, N at level 30, no associativity).
Notation "Γ ⊢ A : B : C" := (Γ ⊢ A : B/\Γ ⊢ B : C) (at level 80, A, B, C at level 30, no associativity).

(** Basic properties of PTS.
  Context Validity: if a judgment is valid, its context is well-formed.*)
Lemma wf_typ : forall Γ t T, Γ ⊢ t : T -> Γ ⊣.
induction 1; eauto.
Qed.

Hint Resolve wf_typ.

(** Inversion Lemmas , one for each kind of term
  from a typing derivation of some particular term, we can
infer informations about its type and subterms.*)

Lemma gen_sort : forall Γ s T, Γ ⊢ !s : T -> exists t, T = !t /\ Ax s t.
inversion 1;subst;repeat eassumption||econstructor.
Qed.

Lemma gen_var : forall Γ x A, Γ ⊢ #x : A -> exists A', A = A' /\ A' ↓ x ⊂ Γ .
inversion 1;subst;repeat eassumption||econstructor.
Qed.

Lemma gen_pi : forall Γ A B T, Γ ⊢ Π(A),B : T -> exists s1 s2 s3,
    T = !s3 /\ Rel s1 s2 s3 /\ Γ ⊢ A : !s1  /\ A::Γ ⊢ B : !s2 .
inversion 1;subst;repeat eassumption||econstructor.
Qed.

Lemma gen_la : forall Γ A M T, Γ ⊢ λ[A],M : T -> exists s1 s2 s3 B,
T = Π(A), B /\ Rel s1 s2 s3 /\ Γ ⊢ A : !s1 /\ A::Γ ⊢ M : B /\ A::Γ ⊢ B : !s2.
inversion 1;subst;repeat eassumption||econstructor.
Qed.

Lemma gen_app : forall Γ M N T, Γ ⊢ M · N : T -> exists A B, T = B[← N] /\ Γ ⊢ M : Π(A),B /\ Γ ⊢ N : A.
inversion 1;subst;repeat eassumption||econstructor.
Qed.

Lemma gen_conv : forall Γ a H T, Γ ⊢ a ∽ H : T -> exists A s, Γ ⊢ a : A /\ Γ ⊢ T:!s /\ Γ ⊢ H : A = T.
inversion 1;subst;repeat eassumption||econstructor.
Qed.

(** Weakening Property: if a judgement is valid, we can insert a well-typed term
  in the context, it will remain valid. This is where the type checking for
  inserting items in a context is done.*)

Theorem weakening: 
(forall Γ   M N, Γ ⊢     M : N -> forall Δ A s n Γ', ins_in_env Δ A n Γ Γ' -> Δ ⊢ A : !s -> Γ' ⊢              M ↑ 1 # n : N ↑ 1 # n ) /\
(forall Γ H M N, Γ ⊢ H : M = N -> forall Δ A s n Γ', ins_in_env Δ A n Γ Γ' -> Δ ⊢ A : !s -> Γ' ⊢ H ↑h 1 # n : M ↑ 1 # n = N ↑ 1 # n ) /\
(forall Γ      , Γ ⊣           -> forall Δ A s n Γ', ins_in_env Δ A n Γ Γ' -> Δ ⊢ A : !s -> Γ' ⊣).
apply typ_induc; simpl in *; intros;eauto.
(*var*)
destruct (le_gt_dec n v).
constructor. eapply H; eauto. destruct i as (AA & ?& ?). exists AA; split. 
rewrite H2; change (S (S v)) with (1+ S v); rewrite_l liftP3; simpl; intuition. eapply ins_item_ge;eauto.
constructor. eapply H; eauto.  eapply ins_item_lift_lt;eauto.
(*abs*)
econstructor; eauto.
(*app*)
change n with (0+n); rewrite_l substP1; simpl.
econstructor; eauto.
(* nil *)
inversion H; subst;eauto.
(* cons *)
inversion H0; subst;eauto.
(* beta *)
change n with (0+n); rewrite_l substP1; simpl.
econstructor;eauto.
(* prod-eq *)
econstructor; [eexact r|eexact r0|eauto..].
rewrite_l_rev liftP2;intuition.
rewrite_r_rev liftP2;intuition.
replace (#0 ∽ H ↑h 1 ↑h 1 # (1 + n)) with ((#0 ∽ H ↑h 1) ↑ 1 # (S n)) by trivial.
replace (1+S n) with (S (0+S n)) by trivial.
rewrite_l_rev substP1;simpl.
eapply H5;eauto. 
(* abs-eq *)
econstructor; [eexact r|eexact r0|eauto..].
rewrite_l_rev liftP2;intuition.
rewrite_r_rev liftP2;intuition.
replace (#0 ∽ H ↑h 1 ↑h 1 # (1 + n)) with ((#0 ∽ H ↑h 1) ↑ 1 # (S n)) by trivial.
replace (1+S n) with (S (0+S n)) by trivial.
rewrite_l_rev substP1;simpl.
eapply H7;eauto.
(* app-eq *) 
econstructor; eauto.
Qed.


Theorem thinning : forall Γ M N A s, Γ ⊢ M : N -> Γ ⊢ A : !s -> A::Γ ⊢ M ↑ 1 : N ↑ 1.
intros;eapply weakening;eassumption||econstructor.
Qed.

Theorem thinning_h : forall Γ H M N A s, Γ ⊢ H : M = N -> Γ ⊢ A : !s -> A::Γ ⊢ H ↑h 1 : M ↑ 1 = N ↑ 1.
intros;eapply weakening;eassumption||econstructor.
Qed.

Theorem thinning_n : forall n Δ Δ', trunc n Δ Δ' -> forall M T , Δ' ⊢ M : T  -> Δ ⊣ -> Δ ⊢ M ↑ n : T ↑ n.
induction n; intros;inversion H; subst.
do 2 rewrite_l lift0; trivial.
change (S n) with (1+n).
replace (M ↑ (1+n)) with ((M ↑ n )↑ 1) by (apply lift_lift).
replace (T ↑ (1+n)) with ((T ↑ n) ↑ 1) by (apply lift_lift).
inversion H1; subst.
apply thinning with s; trivial.
eapply IHn. apply H3. trivial. eauto.
Qed.

Theorem thinning_n_h : forall n Δ Δ' H M N ,trunc n Δ Δ' -> Δ' ⊢ H : M = N -> Δ ⊣ -> Δ ⊢ H ↑h n : M ↑ n = N ↑ n.
induction n;inversion 1;intros;subst.
do 2 rewrite_l lift0; rewrite_r lift0; trivial.
change (S n) with (1+n).
do 2 rewrite_l_rev lift_lift;rewrite_r_rev lift_lift.
inversion H6;subst.
eapply thinning_h with s;[eapply IHn;try eapply wf_typ;eassumption|assumption].
Qed.

(** Substitution Property: if a judgment is valid and we replace a variable by a
  well-typed term of the same type, it will remain valid.*)

Lemma sub_trunc : forall Δ a A n Γ Γ', sub_in_env Δ a A n Γ Γ' -> trunc n Γ' Δ.
induction 1;constructor;trivial.
Qed.


Theorem substitution :
(forall Γ   M N , Γ ⊢  M : N  -> forall Δ a A Γ' n, Δ ⊢ a : A -> sub_in_env Δ a A n Γ Γ' -> Γ ⊣ -> Γ' ⊢          M [ n ← a ]  : N [ n ← a ] ) /\
(forall Γ H M N , Γ ⊢H:M = N  -> forall Δ a A Γ' n, Δ ⊢ a : A -> sub_in_env Δ a A n Γ Γ' -> Γ ⊣ -> Γ' ⊢ H[n←h a]:M [ n ← a ]  = N [ n ← a ] ) /\
(forall Γ      ,  Γ ⊣         -> forall Δ a A Γ' n, Δ ⊢ a : A -> sub_in_env Δ a A n Γ Γ' ->        Γ' ⊣).
apply typ_induc; simpl in *; intros;try (econstructor;eauto;fail).
(* var *)
destruct lt_eq_lt_dec as [ [] | ].
constructor. eapply H; eauto. eapply nth_sub_item_inf. apply H1. intuition. trivial.
destruct i as (AA & ?& ?). subst. rewrite_l substP3; intuition.
set (subst_item H1).
rewrite <- (fun_item i H4). eapply thinning_n. eapply sub_trunc. apply H1. trivial.
eapply H; eauto. constructor. eapply H; eauto. destruct i as (AA & ? &?). subst.
rewrite_l substP3; intuition. exists AA; split. replace (S (v-1)) with v. trivial.
rewrite minus_Sn_m. intuition. destruct v. apply lt_n_O in l; elim l. intuition.
eapply nth_sub_sup. apply H1. destruct v. apply lt_n_O in l; elim l. simpl. rewrite <- minus_n_O.
intuition. rewrite <- pred_of_minus. rewrite <- (S_pred v n l). trivial.
(* app *)
rewrite_l subst_travers. replace (n+1) with (S n) by (rewrite plus_comm; trivial); eauto.
(* wf *)
inversion H0.
inversion H1; subst. eauto.
econstructor. eapply H. apply H0. trivial. eauto.
(* beta *)
rewrite_l subst_travers;replace (n+1) with (S n) by (rewrite plus_comm; trivial);econstructor;eauto.
(* prod-eq *)
econstructor;[exact r|exact r0|eauto..].
rewrite_l_rev substP2;intuition;rewrite_r_rev substP2;intuition.
change (1+S n) with (S(0+S n)).
change (#0 ∽ H ↑h 1 [(1 + n) ←h a]) with ((#0 ∽ H ↑h 1) [(S n) ← a]).
rewrite_l_rev substP4;simpl;eauto.
(* abs-eq *)
econstructor;[exact r|exact r0|eauto..].
rewrite_l_rev substP2;intuition;rewrite_r_rev substP2;intuition.
change (1+S n) with (S(0+S n)).
change (#0 ∽ H ↑h 1 [(1 + n) ←h a]) with ((#0 ∽ H ↑h 1) [(S n) ← a]).
rewrite_l_rev substP4;simpl;eauto.
Qed.

(** Well-formation of contexts: if a context is valid, every term inside
  is well-typed by a sort.*)
Lemma wf_item : forall Γ A n, A ↓ n ∈ Γ -> forall  Γ', Γ ⊣ ->  trunc (S n) Γ Γ' -> exists s, Γ' ⊢ A : !s.
induction 1; intros;inversion H0; subst.
inversion H5; subst;inversion H; subst. exists s; trivial.
inversion H1; subst. apply IHitem;eauto.
Qed.

Lemma wf_item_lift : forall Γ A n ,Γ ⊣  -> A ↓ n ⊂ Γ -> exists s,  Γ ⊢ A  : !s.
destruct 2 as (u & ? & ?);subst.
assert (exists Γ' , trunc (S n) Γ Γ') by (apply item_trunc with u; trivial).
destruct H0 as (Γ' & ?).
destruct (wf_item Γ u n H1 Γ' H H0) as (t &  ?).
exists t. change !t with (!t ↑(S n)).
eapply thinning_n;eauto.
Qed.

(** Properties of equalities*)
Lemma conv_inj : (forall Y H X n, (X ↑  1 # (S n)) [n ←  #0 ∽ H] = (Y ↑  1 # (S n)) [n ←  #0 ∽ H]->X=Y)/\
                  (forall Y H X n, (X ↑h 1 # (S n)) [n ←h #0 ∽ H] = (Y ↑h 1 # (S n)) [n ←h #0 ∽ H]->X=Y).
assert (forall X v H n, (X ↑  1 # (S n)) [n ←  #0 ∽ H] = #v->X=#v) as HH1.
intros;destruct X;[|simpl in H0..];try discriminate;
unfold lift_rec in H0;destruct le_gt_dec;unfold subst_rec in H0;destruct lt_eq_lt_dec as [[]|];try discriminate;try discriminate;injection H0;intros;subst.
simpl in *.
destruct (lt_irrefl n);apply lt_trans with (S v0);[constructor|];assumption.
rewrite <- minus_n_O;reflexivity.
reflexivity.
destruct (lt_irrefl v0);apply le_lt_trans with (n);[apply le_S_n|];assumption.

assert (forall X v H n, (X ↑  1 # (S n)) [n ←  #0 ∽ H] = (#v ↑  1 # (S n)) [n ←  #0 ∽ H]->X=#v) as HH0.
intros;unfold lift_rec in H0 at 2;destruct le_gt_dec;unfold subst_rec in H0 at 2;destruct lt_eq_lt_dec as [[]|];subst.
destruct (lt_irrefl v);apply lt_trans with n;[apply lt_trans with (S v);[constructor|]|];assumption.
destruct (lt_irrefl v);apply lt_trans with (S v);[constructor|assumption].
eapply HH1;rewrite minus_plus in H0;eassumption.
eapply HH1;eassumption.
simpl in H0;destruct X;[|simpl in H0..];try discriminate.
unfold lift_rec in H0;destruct le_gt_dec;unfold subst_rec in H0;destruct lt_eq_lt_dec as [[]|];try discriminate;subst.
destruct (lt_irrefl v);apply lt_trans with (S v);[constructor|assumption].
reflexivity.
injection H0;intros.
apply HH1 in H2;rewrite <- plus_n_O in *;subst.
unfold lift_rec in H0;destruct le_gt_dec. 
destruct le_Sn_n with n;assumption.
unfold subst_rec in H0;destruct lt_eq_lt_dec as [[]|];try (destruct lt_irrefl with n;assumption).
discriminate.
destruct (lt_irrefl v);apply le_lt_trans with n;[apply le_S_n|];assumption.

apply Term_induc;intros;[eapply HH0;eassumption|..];(destruct X;[try (symmetry;eapply HH0;symmetry;eassumption;fail)|..]);
simpl in H0;try discriminate;try injection H0;try injection H1;try injection H2;try injection H3;
intros;f_equal;try eapply H;try eapply H0;try eapply H1;try eassumption.
Qed.

Lemma equality_unique : forall Γ H A B C D, Γ ⊢ H : A = B -> Γ ⊢ H : C = D -> A = C /\ B = D.
intros until 1;revert C D;induction H0;inversion 1;subst;try (split;reflexivity;fail).
edestruct IHtyp_h;[eexact H5|];subst;split;reflexivity.
edestruct IHtyp_h1;[eexact H5|];edestruct IHtyp_h2;[eexact H8|];subst;split;reflexivity.
edestruct IHtyp_h1;[eexact H20|];edestruct IHtyp_h2;[eexact H21|];subst;split;[reflexivity|f_equal;eapply conv_inj;eassumption].
edestruct IHtyp_h1;[eexact H24|];edestruct IHtyp_h2;[eexact H25|];subst;split;[reflexivity|f_equal;eapply conv_inj;eassumption].
edestruct IHtyp_h1;[eexact H13|];edestruct IHtyp_h2;[eexact H16|];subst;split;reflexivity.
Qed.

Lemma beta_type_l : forall Γ a A b B s1 s2 s3, Rel s1 s2 s3 -> Γ ⊢ a : A -> Γ ⊢ A : !s1 
                         -> A::Γ ⊢ b : B -> A::Γ ⊢ B : !s2 -> Γ ⊢ ((λ[A], b)·a) : B[←a].
intros;repeat econstructor;eauto.
Qed.

Lemma beta_type_r : forall Γ a A b B, Γ ⊢ a : A -> A::Γ ⊢ b : B -> Γ ⊢ b[←a] : B[←a].
intros;eapply substitution;eauto.
Qed.

Lemma equality_typing : forall Γ H A B, Γ ⊢ H : A = B -> has_type A Γ /\ has_type B Γ.
unfold has_type;induction 1;eauto;intuition;[exists B[←a];eapply beta_type_l;eauto|exists B[←a];eapply beta_type_r;eauto|
try (repeat econstructor;eauto;fail)..].
econstructor;econstructor;[exact H0|eauto..].
econstructor;econstructor;[exact H0|eauto..].
econstructor;econstructor;[exact H1|eauto..].
Qed.

(** Type Correction: if a judgment is valid, the type is either welltyped
  itself, or syntacticaly a sort. This distinction comes from the fact
  that we abstracted the typing of sorts with [Ax] and that they may be some
  untyped sorts (also called top-sorts).*)
Theorem TypeCorrect : forall Γ M N, Γ ⊢ M : N -> semitype N Γ.
intros; induction H;unfold semitype;eauto.
(*var*)
apply wf_item_lift in H0; auto.
(*app*)
destruct IHtyp1 as [[]|[]]; try discriminate;
apply gen_pi in H1 as (?&s&?&?&?&?&?);subst.
right;exists s.
change (!s) with (!s [← a]);eapply substitution;eauto.
Qed.



(** Equivalence with presentation of PTS in the paper*)
Reserved Notation "Γ ⊢'     M : N" (at level 80, M, N    at level 30, no associativity).
Reserved Notation "Γ ⊣' " (at level 80, no associativity).
Reserved Notation "Γ ⊢' H : M = N" (at level 80, H, M, N at level 30, no associativity).

Inductive simple_wf : Env -> Prop :=
 | lwf_nil  : nil ⊣'
 | lwf_cons : forall Γ A s, Γ ⊢' A : !s -> A::Γ ⊣'
where "Γ ⊣'" := (simple_wf Γ) : F_scope
with simple_typ   : Env -> Term -> Term -> Prop :=
 | lcSort   : forall Γ s t, Ax s t -> Γ ⊣' -> Γ  ⊢' !s : !t
 | lcVar    : forall Γ A v, Γ ⊣' -> A ↓ v  ⊂ Γ -> Γ ⊢' #v : A
 | lcProd   : forall Γ A B s1 s2 s3, Rel s1 s2 s3 -> Γ ⊢' A : !s1 -> A::Γ ⊢' B : !s2 -> Γ ⊢'  Π(A), B : !s3
 | lcAbs    : forall Γ A B b s, A::Γ ⊢' b : B -> Γ ⊢'  Π(A), B : !s -> Γ ⊢' λ[A], b : Π(A), B
 | lcApp    : forall Γ F a A B , Γ ⊢' F : Π(A), B -> Γ ⊢' a : A -> Γ ⊢' F · a : B[←a]
 | lcConv    : forall Γ a A B s H, Γ ⊢' a : A -> Γ ⊢' B : !s -> Γ ⊢' H : A = B -> Γ ⊢' a ∽ H : B
where "Γ ⊢' t : T" := (simple_typ Γ t T) : F_scope
with simple_typ_h : Env -> Prf -> Term -> Term -> Prop :=
 | lcRefl   : forall Γ a A, Γ ⊢' a : A -> Γ ⊢' ρ a : a = a
 | lcSym    : forall Γ H A B, Γ ⊢' H : A = B -> Γ ⊢' H† : B = A
 | lcTrans  : forall Γ H K A B C, Γ ⊢' H : A = B -> Γ ⊢' K : B = C -> Γ ⊢' H•K : A = C
 | lcBeta   : forall Γ a A b B, Γ ⊢' (λ[A], b)·a : B -> Γ ⊢' β((λ[A], b)·a) : (λ[A], b)·a = b[←a]
 | lcProdEq : forall Γ A A' B B' H K s s', Γ ⊢' Π(A), B : !s -> Γ ⊢' Π(A'), B' : !s' 
            -> Γ ⊢' H : A = A' -> A::Γ ⊢' K : B = (B'↑1#1)[←#0∽H↑h1] -> Γ ⊢' {H,[A]K} : Π(A), B = Π(A'), B'
 | lcAbsEq  : forall Γ A A' b b' B B' H K, Γ ⊢' λ[A], b : Π(A), B -> Γ ⊢' λ[A'], b' : Π(A'), B' 
            -> Γ ⊢' H : A = A' -> A::Γ ⊢' K : b = (b'↑1#1)[←#0∽H↑h1] -> Γ ⊢' ⟨H,[A]K⟩ : λ[A], b = λ[A'], b'
 | lcAppEq  : forall Γ F F' a a' B B' H K, Γ ⊢' F · a : B -> Γ ⊢' F' · a' : B'
            -> Γ ⊢' H : F = F' -> Γ ⊢' K : a = a' -> Γ ⊢' H ·h K : F · a = F' · a'
 | lcIota    : forall Γ a B H, Γ ⊢' a ∽ H : B -> Γ ⊢' ι(a∽H) : a = a∽H
where "Γ ⊢' H : A = B" := (simple_typ_h Γ H A B) : F_scope.

Local Hint Constructors simple_typ simple_typ_h simple_wf.

Scheme ltyp_ind'  := Induction for simple_typ   Sort Prop
  with   lwf_ind' := Induction for simple_wf    Sort Prop
  with ltyph_ind' := Induction for simple_typ_h Sort Prop.
Combined Scheme ltyp_induc from ltyp_ind', ltyph_ind',lwf_ind'.



Lemma simple2normal : (forall Γ   M N, Γ ⊢'     M : N -> Γ ⊢     M : N)/\
                      (forall Γ H M N, Γ ⊢' H : M = N -> Γ ⊢ H : M = N)/\
                      (forall Γ      , Γ ⊣'           -> Γ ⊣).
Proof.
apply ltyp_induc;intros;eauto.
(*abs*)
inversion H0;subst;econstructor;eassumption.
(*beta*)
inversion H;inversion H3;subst;econstructor;eassumption.
(*prod-eq*)
inversion H0;inversion H1;subst;econstructor;[eexact H8|..];eassumption.
(*abs-eq*)
inversion H0;inversion H1;subst;econstructor;[eexact H7|..];eassumption.
(*prod-eq*)
inversion H0;inversion H1;subst;econstructor;eassumption.
(*iota*)
inversion H0;subst;econstructor;eassumption.
Qed.

Lemma normal2simple : (forall Γ   M N, Γ ⊢     M : N -> Γ ⊢'     M : N)/\
                      (forall Γ H M N, Γ ⊢ H : M = N -> Γ ⊢' H : M = N)/\
                      (forall Γ,       Γ ⊣           -> Γ ⊣').
Proof.
apply typ_induc;intros;eauto.
(*abs-eq*)
econstructor;eassumption||econstructor;eassumption||econstructor;[eexact r|..];eassumption.
Qed.

Lemma normal_equiv_simple : (forall Γ   M N, Γ ⊢     M : N <-> Γ ⊢'     M : N)/\
                            (forall Γ H M N, Γ ⊢ H : M = N <-> Γ ⊢' H : M = N)/\
                            (forall Γ      , Γ ⊣           <-> Γ ⊣').
repeat split;apply simple2normal||apply normal2simple.
Qed.

End f_typ_mod.
