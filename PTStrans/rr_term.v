(** * Our Definition of  PTSf containg the Resing Rules as well.  *)

Require Import base.
Require Import List Lt Le Gt Plus Minus Peano_dec Compare_dec.
Require Import f_term f_env f_typ.

Module Type resizing_env (X : term_sig) (Y : pts_sig X) (FTM : f_term_mod X) (FEM : f_env_mod X FTM).
  Import X Y FTM FEM.
  Include (f_typ_mod X Y FTM FEM).

  Parameter ΓΓ : Env.
  Parameters s t : Sorts.
  Parameters AA BB ff gg η ε : Term.
  Parameter AAtyp : forall n Δ, trunc n Δ ΓΓ -> Δ ⊢ AA : !s.
  Parameter BBtyp : forall n Δ, trunc n Δ ΓΓ -> Δ ⊢ BB : !t.
  Parameter fftyp : forall n Δ, trunc n Δ ΓΓ -> Δ ⊢ ff : Π(AA), BB ↑ 1.
  Parameter ggtyp : forall n Δ, trunc n Δ ΓΓ -> Δ ⊢ gg : Π(BB), AA ↑ 1.
  Parameter ηtyp  : forall n Δ, trunc n Δ ΓΓ -> Δ ⊢ η  : Π(AA), Id (AA ↑ 1) ((gg ↑ 1) · ((ff ↑ 1) · #0)) #0.
  Parameter εtyp  : forall n Δ, trunc n Δ ΓΓ -> Δ ⊢ ε  : Π(BB), Id (BB ↑ 1) ((ff ↑ 1) · ((gg ↑ 1) · #0)) #0.

End resizing_env.

(** We assume that we have a context Γ in which everything required for the resizing rule is defined. *)
Module Type rr_term_mod (X : term_sig) (Y : pts_sig X) (FTM : f_term_mod X) (FEM : f_env_mod X FTM)
                        (RE : resizing_env X Y FTM FEM).
  Import X Y.

  Inductive Term : Set :=
  | Var    : Vars  -> Term
  | Sort   : Sorts -> Term
  | Prod   : Term  -> Term -> Term
  | Abs    : Term  -> Term -> Term
  | App    : Term  -> Term -> Term
  | Id     : Term  -> Term -> Term -> Term
  | Rfl    : Term  -> Term -> Term
  | J      : Term  -> Term -> Term -> Term -> Term -> Term -> Term
  | Conv   : Term  -> Prf  -> Term
  | AA     : Term
  | RRAA   : Term
  | Inj    : Term  -> Term
  | Proj   : Term  -> Term
  with Prf : Set :=
  | Refl   : Term  -> Prf
  | Sym    : Prf   -> Prf
  | Trans  : Prf   -> Prf  -> Prf
  | Beta   : Term  -> Prf
  | ProdEq : Prf   -> Term -> Prf  -> Prf
  | AbsEq  : Prf   -> Term -> Prf  -> Prf
  | AppEq  : Prf   -> Prf  -> Prf
  | Iota   : Term  -> Prf
  | IdEq   : Prf   -> Prf  -> Prf  -> Prf
  | RflEq  : Prf   -> Prf  -> Prf
  | JEq    : Prf   -> Prf  -> Prf  -> Prf  -> Prf  -> Prf  -> Prf
  | JRed   : Term  -> Prf
  | PI     : Term  -> Prf
  | IP     : Term  -> Prf
  .

  Notation "! s" := (Sort s) (at level 1) : RR_scope.
  Notation "# v" := (Var v) (at level 1) : RR_scope.
  Notation "'Π' ( U ) , V " := (Prod U V) (at level 20, U, V at level 30) : RR_scope.
  Notation "'λ' [ U ] , v " := (Abs U v) (at level 20, U , v at level 30) : RR_scope.
  Notation "x · y" := (App x y) (at level 15, left associativity) : RR_scope.
  Notation "A ∽ H" := (Conv A H) (at level 15) : RR_scope.
  Notation "'ρ' A" := (Refl A) (at level 6) : RR_scope. 
  Notation "H †" := (Sym H) (at level 6) : RR_scope.
  Notation "H1 • H2" := (Trans H1 H2) (at level 15, left associativity) : RR_scope.
  Notation "'β' A" := (Beta A) (at level 6) : RR_scope.
  Notation "{ H1 , [ A ] H2 }" := (ProdEq H1 A H2) (at level 15) : RR_scope.
  Notation "⟨ H1 , [ A ] H2 ⟩" := (AbsEq H1 A H2) (at level 15, left associativity) : RR_scope.
  Notation "H1 ·h H2" := (AppEq H1 H2) (at level 15, left associativity) : RR_scope.
  Notation "'ι' A" := (Iota A) (at level 6) : RR_scope.

  Reserved Notation " t ↑  x # n " (at level 5, x at level 0, left associativity).
  Reserved Notation " t ↑h x # n " (at level 5, x at level 0, left associativity).

  Delimit Scope RR_scope with RR.

  Open Scope RR_scope.

  Scheme Term_ind' := Induction for Term Sort Prop
                     with Prf_ind' := Induction for Prf Sort Prop.

  Combined Scheme Term_induc from Term_ind', Prf_ind'.

  Fixpoint lift_rec (n:nat) (k:nat) (T:Term) {struct T} := match T with
    | # x =>  if le_gt_dec k x then Var (n+x) else Var x
    | ! s => Sort s
    | M · N =>  App (M ↑ n # k) (N ↑ n # k)
    | Π ( A ), B => Π (A ↑ n # k), (B ↑ n # (S k))
    | λ [ A ], M => λ [A ↑ n # k], (M ↑ n # (S k)) 
    | A ∽ H => A ↑ n # k ∽ H ↑h n # k
    | Id A u v => Id (A ↑ n # k) (u ↑ n # k) (v ↑ n # k)
    | Rfl A u => Rfl (A ↑ n # k) (u ↑ n # k)
    | J A C b u v p => J (A ↑ n # k) (C ↑ n # k) (b ↑ n # k) (u ↑ n # k) (v ↑ n # k) (p ↑ n # k)
    | AA => AA
    | RRAA => RRAA
    | Inj t => Inj (t ↑ n # k)
    | Proj t => Proj (t ↑ n # k)
  end  
  where "t ↑ n # k" := (lift_rec n k t) : RR_scope
  with lift_rec_h (n:nat) (k:nat) (H:Prf) {struct H} := match H with
   | ρ A => ρ (A ↑ n # k)
   | H† => (H ↑h n # k)†
   | H•K => (H ↑h n # k)•(K ↑h n # k)
   | β A => β(A ↑ n # k)
   | H ·h K => (H ↑h n # k) ·h (K ↑h n # k)
   | {H,[A]K} => {H ↑h n # k,[A ↑ n # k]K ↑h n # (S k)}
   | ⟨H,[A]K⟩ => ⟨H ↑h n # k,[A ↑ n # k]K ↑h n # (S k)⟩
   | ι A => ι(A ↑ n # k)
   | IdEq H1 H2 H3 => IdEq (H1 ↑h n # k) (H2 ↑h n # k) (H3 ↑h n # k)
   | RflEq H1 H2 => RflEq (H1 ↑h n # k) (H2 ↑h n # k)
   | JEq HA HC Hb Hu Hv Hp => JEq (HA ↑h n # k) (HC ↑h n # k) (Hb ↑h n # k) (Hu ↑h n # k) (Hv ↑h n # k) (Hp ↑h n # k)
   | JRed T => JRed (T ↑ n # k)
   | PI t => PI (t ↑ n # k)
   | IP t => IP (t ↑ n # k)
  end  
  where "t ↑h n # k" := (lift_rec_h n k t) : RR_scope.

  Notation " t ↑  n " := (lift_rec   n 0 t) (at level 5, n at level 0, left associativity) : RR_scope.
  Notation " t ↑h n " := (lift_rec_h n 0 t) (at level 5, n at level 0, left associativity) : RR_scope.

  Lemma inv_lift : (forall M N n m, M ↑  n # m = N ↑  n # m -> M = N) /\
                 (forall M N n m, M ↑h n # m = N ↑h n # m -> M = N).
  Admitted.

  Lemma lift_rec0 : (forall M n, M ↑ 0 # n = M) /\ (forall H n, H ↑h 0 # n = H).
  Admitted.

  Lemma lift0 : (forall M, M ↑ 0 = M) /\ (forall H, H ↑h 0 = H).
    destruct lift_rec0; intuition.
  Qed.

  Lemma liftP1 : (forall M i j k, (M ↑  j # i) ↑  k # (j+i) = M ↑  (j+k) # i) /\
               (forall H i j k, (H ↑h j # i) ↑h k # (j+i) = H ↑h (j+k) # i).
  Admitted.

  Lemma liftP2: (forall M i j k n, i <= n -> (M ↑ j # i) ↑ k # (j+n) = (M ↑ k # n) ↑ j # i)/\
              (forall H i j k n, i <= n -> (H ↑h j # i) ↑h k # (j+n) = (H ↑h k # n) ↑h j # i).
  Admitted.

  Lemma liftP3 : (forall M i k j n , i <= k -> k <= (i+n) -> (M ↑  n # i) ↑  j # k = M ↑  (j+n) # i) /\
               (forall H i k j n , i <= k -> k <= (i+n) -> (H ↑h n # i) ↑h j # k = H ↑h (j+n) # i).
  Admitted.

  Lemma lift_lift : (forall M n m, (M ↑  m) ↑  n = M ↑  (n+m)) /\
                    (forall H n m, (H ↑h m) ↑h n = H ↑h (n+m)).
    destruct liftP3;intuition.
  Qed.

  Reserved Notation "t [ x ←  u ]" (at level 5, x at level 0, left associativity).
  Reserved Notation "t [ x ←h u ]" (at level 5, x at level 0, left associativity).

  Fixpoint subst_rec U T n {struct T} :=
    match T with
    | # x => match (lt_eq_lt_dec x n) with
            | inleft (left _) => # x     (* (v < n) *)
            | inleft (right _) => U ↑ n  (* (v = n) *)
            | inright _ => # (x - 1)     (* (v > n) *)
            end
    | ! s => ! s
    | M · N => (M [ n ← U ]) · ( N [ n ← U ]) 
    | Π ( A ), B => Π ( A [ n ← U ] ), (B [ S n ← U ]) 
    | λ [ A ], M => λ [ A [ n ← U ] ], (M [ S n ← U ]) 
    | A ∽ H => A [ n ← U ] ∽ H [ n ←h U ]
    | Id A u v => Id (A [ n ← U ]) (u [ n ← U ]) (v [ n ← U ])
    | Rfl A u => Rfl (A [ n ← U ]) (u [ n ← U ])
    | J A C b u v p => J (A [ n ← U ]) (C [ n ← U ]) (b [ n ← U ]) (u [ n ← U ]) (v [ n ← U ]) (p [ n ← U ])
    | AA => AA
    | RRAA => RRAA
    | Inj t => Inj (t [ n ← U ])
    | Proj t => Proj (t [ n ← U ])
    end
    where " t [ n ← w ] " := (subst_rec w t n) : RR_scope
  with subst_rec_h U H n {struct H} := match H with
    | ρ A => ρ A [ n ← U ]
    | H† => H [ n ←h U ] †
    | H•K => H[ n ←h U ]•K[ n ←h U ]
    | β A => β A[ n ← U ]
    | H ·h K => H[ n ←h U ] ·h K[ n ←h U ]
    | {H,[A]K} => {H[ n ←h U ],[A[ n ← U ]]K[ S n ←h U ]}
    | ⟨H,[A]K⟩ => ⟨H[ n ←h U ],[A[ n ← U ]]K[ S n ←h U ]⟩
    | ι A => ι A [ n ← U ]
    | IdEq HA Hu Hv => IdEq (HA [ n ←h U ]) (Hu [ n ←h U ]) (Hv [ n ←h U ])
    | RflEq HA Hu => RflEq (HA [ n ←h U ]) (Hu [ n ←h U ])
    | JEq HA HC Hb Hu Hv Hp => JEq (HA [ n ←h U ]) (HC [ n ←h U ]) (Hb [ n ←h U ]) (Hu [ n ←h U ]) (Hv [ n ←h U ]) (Hp [ n ←h U ])
    | JRed T => JRed (T [ n ← U ])
    | PI t => PI (t [ n ← U ])
    | IP t => IP (t [ n ← U ])
    end
    where " t [ n ←h w ] " := (subst_rec_h w t n) : RR_scope.

  Notation " t [ ← w ] " := (subst_rec   w t 0) (at level 5) : RR_scope.
  Notation " t [ ←h w ] " := (subst_rec_h w t 0) (at level 5) : RR_scope.

  Lemma substP1: (forall M N i j k, ( M [ j ←  N] ) ↑  k # (j+i) = (M ↑  k # (S (j+i))) [ j ←  (N ↑ k # i ) ])/\
                 (forall H N i j k, ( H [ j ←h N] ) ↑h k # (j+i) = (H ↑h k # (S (j+i))) [ j ←h (N ↑ k # i ) ]).
  Admitted.

  Lemma substP2: (forall M N i j n, i <= n -> (M ↑  j # i ) [ j+n ←  N ] = ( M [ n ←  N]) ↑  j # i)/\
                 (forall H N i j n, i <= n -> (H ↑h j # i ) [ j+n ←h N ] = ( H [ n ←h N]) ↑h j # i).
  Admitted.

  Lemma substP3: (forall M N i k n, i <= k -> k <= i+n ->  (M ↑  (S n) # i) [ k←  N] = M ↑  n # i)/\
                 (forall H N i k n, i <= k -> k <= i+n ->  (H ↑h (S n) # i) [ k←h N] = H ↑h n # i).
  Admitted.

  Lemma substP4: (forall M N P i j, (M [ i← N]) [i+j ← P] = (M [S(i+j) ← P]) [i← N[j← P]])/\
                 (forall H N P i j, (H [ i←h N]) [i+j ←h P] = (H [S(i+j) ←h P]) [i←h N[j← P]]).
  Admitted.

  Lemma subst_travers : (forall  M N P n, (M [←  N]) [n ←  P] = (M [n+1 ←  P])[←  N[n← P]])/\
                        (forall  H N P n, (H [←h N]) [n ←h P] = (H [n+1 ←h P])[←h N[n← P]]).
    destruct substP4;split;intros;simpl;rewrite plus_comm;
    change (1+n) with (S n); change n with (0+n); intuition.
  Qed.

  Lemma erasure_lem1 : (forall a n, a = (a ↑  1 # (S n)) [n ←  #0]) /\
                       (forall H n, H = (H ↑h 1 # (S n)) [n ←h #0]).
  Admitted.

  Lemma erasure_lem3 : (forall n m t, m>n->#m = (#m ↑ 1 # (S n)) [n ←  t]).
    intros. 
    unfold lift_rec;destruct le_gt_dec.
    unfold subst_rec;destruct lt_eq_lt_dec as [[]|];simpl in *.
    destruct (lt_irrefl n). apply lt_trans with m;[assumption|apply lt_trans with (S m);[do 2 constructor|assumption]].
    subst. destruct (lt_irrefl m). apply lt_trans with (S m);[do 2 constructor|assumption].
    rewrite <- minus_n_O;reflexivity.
    destruct (lt_irrefl n). apply lt_le_trans with m;[|apply le_S_n];assumption. 
  Qed.

  Lemma lift_is_lift_sublemma : forall j v, j<v->exists w,#v=w↑1#j.
    intros. exists #(v-1). assert (S(v-1)=v). 
    rewrite (minus_Sn_m v 1);[simpl;rewrite <- (minus_n_O v);reflexivity|
                              unfold lt in H;apply le_trans with (S j);[apply le_n_S;apply le_0_n|assumption]].
    simpl;destruct le_gt_dec. rewrite H0;trivial. 
    destruct lt_irrefl with j;unfold gt in g;unfold lt in g. rewrite H0 in g. apply lt_le_trans with v;assumption.
  Qed.

  Lemma lift_is_lift : (forall N A n i j,N ↑  i # n=A ↑  1 # j -> j<n -> exists M,N=M ↑  1 # j) /\
                       (forall N A n i j,N ↑h i # n=A ↑h 1 # j -> j<n -> exists M,N=M ↑h 1 # j).
  Admitted.

  Lemma subst_is_lift : (forall N T A n j, N [n ←  T]=A↑ 1#j->j<n->exists M,N=M↑ 1#j) /\
                      (forall N T A n j, N [n ←h T]=A↑h1#j->j<n->exists M,N=M↑h1#j).
  Admitted.

End rr_term_mod.


