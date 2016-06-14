(** * Term definition for PTSf and de Bruijn manipulation . *)

Require Import base.
Require Import List Lt Le Gt Plus Minus Peano_dec Compare_dec.



Module Type f_term_mod (X: term_sig).
  Import X.
(** Term syntax, extended with convertibility proofs .*)

Inductive Term : Set:=
 | Var    : Vars  -> Term
 | Sort   : Sorts -> Term
 | Prod   : Term  -> Term -> Term
 | Abs    : Term  -> Term -> Term
 | App    : Term  -> Term -> Term
 | Id     : Term  -> Term -> Term -> Term
 | Rfl    : Term  -> Term -> Term
 | J      : Term  -> Term -> Term -> Term -> Term -> Term -> Term
 | Conv   : Term  -> Prf  -> Term
with Prf : Set :=
 | Refl   : Term  -> Prf
 | Sym    : Prf   -> Prf
 | Trans  : Prf   -> Prf  -> Prf
 | Beta   : Term  -> Prf
 | ProdEq : Prf   -> Term -> Prf -> Prf
 | AbsEq  : Prf   -> Term -> Prf -> Prf
 | AppEq  : Prf   -> Prf  -> Prf
 | Iota   : Term  -> Prf
 | IdEq   : Prf   -> Prf  -> Prf -> Prf
 | RflEq  : Prf   -> Prf  -> Prf
 | JEq    : Prf   -> Prf  -> Prf -> Prf -> Prf -> Prf -> Prf
 | JRed   : Term  -> Prf
.

(**instead of a bar, reflexivity is denoted by ρ. Adding a convertibility proof to a term is denoted by ★*)

Notation "! s" := (Sort s) (at level 1) : F_scope.
Notation "# v" := (Var v) (at level 1) : F_scope.
Notation "'Π' ( U ) , V " := (Prod U V) (at level 20, U, V at level 30) : F_scope.
Notation "'λ' [ U ] , v " := (Abs U v) (at level 20, U , v at level 30) : F_scope.
Notation "x · y" := (App x y) (at level 15, left associativity) : F_scope.
Notation "A ∽ H" := (Conv A H) (at level 15) : F_scope.
Notation "'ρ' A" := (Refl A) (at level 6) : F_scope. 
Notation "H †" := (Sym H) (at level 6) : F_scope.
Notation "H1 • H2" := (Trans H1 H2) (at level 15, left associativity) : F_scope.
Notation "'β' A" := (Beta A) (at level 6) : F_scope.
Notation "{ H1 , [ A ] H2 }" := (ProdEq H1 A H2) (at level 15) : F_scope.
Notation "⟨ H1 , [ A ] H2 ⟩" := (AbsEq H1 A H2) (at level 15, left associativity) : F_scope.
Notation "H1 ·h H2" := (AppEq H1 H2) (at level 15, left associativity) : F_scope.
Notation "'ι' A" := (Iota A) (at level 6) : F_scope.

Reserved Notation " t ↑  x # n " (at level 5, x at level 0, left associativity).
Reserved Notation " t ↑h x # n " (at level 5, x at level 0, left associativity).

Delimit Scope F_scope with F.

Open Scope F_scope.

Scheme Term_ind' := Induction for Term Sort Prop
      with Prf_ind' := Induction for Prf Sort Prop.

Combined Scheme Term_induc from Term_ind', Prf_ind'.

(** In order to deal with variable bindings and captures, we need a lift
function to deal with free and bounded variables.


   M ↑ n # m recursivly adds n to all variables that are
   above m in M. H ↑h n # m does the same for convertibility proofs*)
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
 end  
   where "t ↑ n # k" := (lift_rec n k t) : F_scope
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
 end  
 where "t ↑h n # k" := (lift_rec_h n k t) : F_scope.

Notation " t ↑  n " := (lift_rec   n 0 t) (at level 5, n at level 0, left associativity) : F_scope.
Notation " t ↑h n " := (lift_rec_h n 0 t) (at level 5, n at level 0, left associativity) : F_scope.

(** Some basic properties of the lift function. That is everything we will
ever need to handle de Bruijn indexes *)

Lemma inv_lift : (forall M N n m, M ↑  n # m = N ↑  n # m -> M = N) /\
                 (forall M N n m, M ↑h n # m = N ↑h n # m -> M = N).
apply Term_induc;try destruct N;try destruct K;intros;simpl in *;
(**solve all trivial cases*)
try discriminate;try intuition;
(**solve all trivial cases involving a variable*)
(try (destruct (le_gt_dec m v) ; discriminate));
(**solve the induction steps with three constructors (PiEq and LaEq)*)
try (injection H2;intros;rewrite (H N1 n m H5);rewrite (H0 t0 n m H4);rewrite (H1 N2 n (S m) H3);reflexivity);
(**solve all steps with 2 constructors*)
try (injection H1;intros;rewrite (H N1 n m H3)||rewrite (H N n m H3);rewrite (H0 N2 n m H2)
   ||rewrite (H0 N2 n (S m) H2)||rewrite (H0 p0 n m H2);reflexivity);
(**1 constructor*)
try (injection H0;intros;rewrite (H t0 n m H1)||rewrite (H N n m H1);reflexivity).
destruct (le_gt_dec m v); destruct (le_gt_dec m v0); injection H; intros; subst; intuition.
apply plus_reg_l in H0; rewrite H0; trivial. 
elim (lt_irrefl m). apply le_lt_trans with v. trivial. induction n; intuition.
elim (lt_irrefl v0). apply lt_le_trans with m. induction n; intuition. trivial.
Admitted.

Lemma lift_rec0 : (forall M n, M ↑ 0 # n = M) /\ (forall H n, H ↑h 0 # n = H).
apply Term_induc;intros;simpl;try rewrite H;try rewrite H0;try rewrite H1;try rewrite H2;try reflexivity.
destruct (le_gt_dec n v); reflexivity.
Admitted.

Lemma lift0 : (forall M, M ↑ 0 = M) /\ (forall H, H ↑h 0 = H).
destruct lift_rec0; intuition.
Qed.

Lemma liftP1 : (forall M i j k, (M ↑  j # i) ↑  k # (j+i) = M ↑  (j+k) # i) /\
               (forall H i j k, (H ↑h j # i) ↑h k # (j+i) = H ↑h (j+k) # i).
apply Term_induc;intros;simpl;try rewrite <- H;try rewrite <- H0; try rewrite <- H1;
try (replace (j+S i) with (S(j+i)) by intuition);try reflexivity.
destruct le_gt_dec;simpl;destruct le_gt_dec; 
try (rewrite plus_assoc;replace (k+j) with (j+k) by (apply plus_comm));try reflexivity.
apply plus_gt_reg_l in g. elim (lt_irrefl v). apply lt_le_trans with i; intuition.
elim (lt_irrefl v). apply lt_le_trans with i; intuition. induction j; intuition.
Admitted.

Lemma liftP2: (forall M i j k n, i <= n -> (M ↑ j # i) ↑ k # (j+n) = (M ↑ k # n) ↑ j # i)/\
              (forall H i j k n, i <= n -> (H ↑h j # i) ↑h k # (j+n) = (H ↑h k # n) ↑h j # i).
(**solve all cases except the variable case*)
apply Term_induc;intros;simpl;try replace (S(j+n)) with (j+S n) by intuition;
try rewrite H by intuition;try rewrite H0 by intuition;try rewrite H1 by intuition;try reflexivity.
(**variable case*)
destruct (le_gt_dec i v); destruct (le_gt_dec n v); simpl;destruct le_gt_dec;destruct le_gt_dec;try intuition;
[|elim (lt_irrefl v); try (apply lt_le_trans with i;trivial;try (apply le_trans with n;trivial;fail);fail); 
try (try (apply plus_gt_reg_l in g);try (apply plus_le_reg_l in l0); try (apply le_trans with n;trivial);fail)..].

rewrite 2! plus_assoc. replace (k+j) with (j+k) by (apply plus_comm).  trivial. 
apply lt_le_trans with i;trivial. induction k; intuition.
apply lt_le_trans with n;intuition. induction l;intuition.
Admitted.

Lemma liftP3 : (forall M i k j n , i <= k -> k <= (i+n) -> (M ↑  n # i) ↑  j # k = M ↑  (j+n) # i) /\
               (forall H i k j n , i <= k -> k <= (i+n) -> (H ↑h n # i) ↑h j # k = H ↑h (j+n) # i).
apply Term_induc;intros;simpl;
try rewrite H; intuition; try rewrite H0; intuition; try rewrite H1;intuition;
try change (S i+n) with (S(i+n));intuition.

destruct (le_gt_dec i v); simpl.
destruct (le_gt_dec k (n+v)); intuition.
elim (lt_irrefl (i+n)). apply lt_le_trans with k;trivial.
apply le_lt_trans with (n+v);trivial. rewrite plus_comm;intuition.
destruct (le_gt_dec k v); intuition. elim (lt_irrefl k).
apply lt_le_trans with i;trivial.  apply le_lt_trans with v;intuition.
Admitted.

Lemma lift_lift : (forall M n m, (M ↑  m) ↑  n = M ↑  (n+m)) /\
                  (forall H n m, (H ↑h m) ↑h n = H ↑h (n+m)).
destruct liftP3;intuition.
Qed.


(** We will consider the usual implicit substitution without variable capture
(this is where the lift operator comes in handy).
   
M [ n ← N ] replaces the variable n in M by the term N and M [ n ←h N ] does the same for convertibility proofs.
  *)

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
end
      where " t [ n ← w ] " := (subst_rec w t n) : F_scope
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
end
      where " t [ n ←h w ] " := (subst_rec_h w t n) : F_scope.
    


Notation " t [ ← w ] " := (subst_rec   w t 0) (at level 5) : F_scope.
Notation " t [ ←h w ] " := (subst_rec_h w t 0) (at level 5) : F_scope.

(** Some basic properties of the substitution function. Again, we will only need
a few functions to deal with indexes. *)

Lemma substP1: (forall M N i j k, ( M [ j ←  N] ) ↑  k # (j+i) = (M ↑  k # (S (j+i))) [ j ←  (N ↑ k # i ) ])/\
               (forall H N i j k, ( H [ j ←h N] ) ↑h k # (j+i) = (H ↑h k # (S (j+i))) [ j ←h (N ↑ k # i ) ]).
apply Term_induc;intros;
[|simpl;
try replace (S(S(j+i))) with (S((S j)+i)) by intuition;
try rewrite H; intuition; try rewrite H0; intuition;
try rewrite <- (H0 N i (S j)  k );try rewrite <- (H1 N i (S j) k);intuition..].
simpl (#v [j ← N] ↑ k # (j+i)).
change (#v ↑ k # (S (j+i))) with  (if le_gt_dec (S (j+i)) v then #(k+v) else #v).
destruct (lt_eq_lt_dec v j) as [[] | ].
destruct (le_gt_dec (S (j+i)) v).
elim (lt_irrefl v). apply lt_le_trans with j; intuition.
apply le_trans with (S (j+i)); intuition.
simpl.
destruct (le_gt_dec (j+i) v).
elim (lt_irrefl v). apply lt_le_trans with j; intuition. apply le_trans with (j+i); intuition.
destruct (lt_eq_lt_dec v j) as [[] | ]. trivial.
subst. elim (lt_irrefl j);trivial.
elim (lt_irrefl j); apply lt_trans with v; trivial.
destruct (le_gt_dec (S(j+i)) v). subst.
elim (lt_irrefl j). apply lt_le_trans with (S (j+i)). intuition. trivial.
simpl. destruct (lt_eq_lt_dec v j) as [[] | ].
subst. elim (lt_irrefl j); trivial.
apply liftP2; intuition.
subst. elim (lt_irrefl j); trivial.
destruct (le_gt_dec (S (j+i)) v).
simpl.
destruct (le_gt_dec (j+i) (v-1)). destruct (lt_eq_lt_dec (k+v) j) as [[] | ].
elim (lt_irrefl j). apply lt_le_trans with v. trivial. induction k; intuition.
subst. elim (lt_irrefl v). apply lt_le_trans with (S(k+v+i)). intuition. trivial.
destruct v. apply lt_n_O in l; elim l. rewrite <- 2! pred_of_minus. replace (k+ S v) with (S (k+v)) by intuition.
simpl. trivial.
elim (lt_irrefl v). apply lt_le_trans with (S (j+i)). destruct v. apply lt_n_O in l; elim l. 
rewrite <- pred_of_minus in g. simpl in g. intuition. trivial.
simpl.
destruct (le_gt_dec (j+i) (v-1)). destruct (lt_eq_lt_dec v j) as [[] | ].
elim (lt_irrefl j); apply lt_trans with v; trivial.
subst. elim (lt_irrefl j); trivial.
elim (lt_irrefl v). apply lt_le_trans with (S (j+i)). intuition. 
destruct v. apply lt_n_O in l; elim l. rewrite <- pred_of_minus in l0. simpl in l0. intuition.
destruct (lt_eq_lt_dec) as [[] | ]. elim (lt_irrefl j); apply lt_trans with v; trivial.
subst. elim (lt_irrefl j); trivial. trivial.
Admitted.

Lemma substP2: (forall M N i j n, i <= n -> (M ↑  j # i ) [ j+n ←  N ] = ( M [ n ←  N]) ↑  j # i)/\
               (forall H N i j n, i <= n -> (H ↑h j # i ) [ j+n ←h N ] = ( H [ n ←h N]) ↑h j # i).
apply Term_induc;intros;simpl;
try rewrite H; intuition; try rewrite H0; intuition;
try rewrite <- (H0 N (S i) j (S n)); try rewrite <- (H1 N (S i) j (S n)); intuition;
replace (S(j+n)) with (j+(S n)) by intuition;try reflexivity.
try replace (S(S(j+i))) with (S((S j)+i)) by intuition;
try rewrite H; intuition; try rewrite H0; intuition; try rewrite H1; intuition;
try rewrite <- (H0 N i (S j)  k );try rewrite <- (H1 N i (S j) k);intuition.
destruct (le_gt_dec i v); destruct (lt_eq_lt_dec v n) as [[] | ].
simpl.
destruct (le_gt_dec i v).  destruct (lt_eq_lt_dec (j+v) (j+n)) as [[] | ].
reflexivity.
apply plus_reg_l in e. subst. elim (lt_irrefl n); trivial.
apply plus_lt_reg_l in l2. elim (lt_asym v n); trivial.
elim (lt_irrefl i). apply le_lt_trans with v; intuition. subst.
simpl.
destruct (lt_eq_lt_dec (j+n) (j+n)) as [[] | ].
apply lt_irrefl in l0; elim l0.
symmetry.
apply liftP3; intuition.
apply lt_irrefl in l0; elim l0.
simpl.
destruct (le_gt_dec i (v-1)). destruct (lt_eq_lt_dec (j+v) (j+n))as [[] | ].
apply plus_lt_reg_l in l2. elim (lt_asym  v n ); trivial.
apply plus_reg_l in e; subst. elim (lt_irrefl n); trivial.
destruct v. apply lt_n_O in l0; elim l0. rewrite <- 2! pred_of_minus. replace (j+ S v) with (S (j+v)) by intuition.
simpl. trivial.
unfold gt in g. unfold lt in g. rewrite <- pred_of_minus in g. 
rewrite <- (S_pred  v n l0) in g.
elim (lt_irrefl n). apply lt_le_trans with v; trivial. apply le_trans with i; trivial.
simpl. 
destruct (le_gt_dec i v).  elim (lt_irrefl i). apply le_lt_trans with v; trivial.
destruct (lt_eq_lt_dec v (j+n)) as [[] | ]. reflexivity.
subst. elim (lt_irrefl n). apply le_lt_trans with (j+n); intuition. 
elim (lt_irrefl n). apply lt_trans with v.  apply le_lt_trans with (j+n); intuition. trivial.
simpl. subst. 
elim (lt_irrefl n). apply lt_le_trans with i; intuition.
simpl. elim (lt_irrefl n). apply lt_le_trans with v; intuition.
apply le_trans with i; intuition.
Admitted.


Lemma substP3: (forall M N i k n, i <= k -> k <= i+n ->  (M ↑  (S n) # i) [ k←  N] = M ↑  n # i)/\
               (forall H N i k n, i <= k -> k <= i+n ->  (H ↑h (S n) # i) [ k←h N] = H ↑h n # i).
apply Term_induc;intros;simpl;
try rewrite H; intuition; try rewrite H0; intuition; try rewrite H1; intuition; 
replace (S i + n) with (S (i+n));intuition.

destruct (le_gt_dec i v).
unfold subst_rec.
destruct (lt_eq_lt_dec (S(n+v)) k) as [[] | ].
elim (lt_irrefl (i+n)). apply lt_le_trans with k; intuition.
apply le_lt_trans with (v+n). intuition. rewrite plus_comm; intuition.
subst. replace (i+n) with (n+i) in H0 by (apply plus_comm) . replace (S (n+v)) with (n + S v) in H0 by intuition. 
apply plus_le_reg_l in H0. elim (lt_irrefl i). apply le_lt_trans with v; intuition.
simpl. rewrite <- minus_n_O. trivial.
simpl. destruct (lt_eq_lt_dec v k) as [[] | ].
reflexivity. subst. elim (lt_irrefl i). apply le_lt_trans with k; intuition.
elim (lt_irrefl k). apply lt_trans with v; trivial. apply lt_le_trans with i; intuition.
Admitted.

Lemma substP4: (forall M N P i j, (M [ i← N]) [i+j ← P] = (M [S(i+j) ← P]) [i← N[j← P]])/\
               (forall H N P i j, (H [ i←h N]) [i+j ←h P] = (H [S(i+j) ←h P]) [i←h N[j← P]]).
apply Term_induc;intros;simpl;
[|(try rewrite H; intuition;replace (S(S(i+j))) with (S((S i)+ j)) by intuition; 
try rewrite <- H0; intuition; replace (S(i+j)) with ((S i)+ j) by intuition; 
try rewrite H1; intuition)..].
destruct (lt_eq_lt_dec v i) as [[] | ] ; destruct (lt_eq_lt_dec v (S(i+j))) as [[] | ].
simpl.
destruct (lt_eq_lt_dec v (i+j)) as [[] | ]. destruct (lt_eq_lt_dec v i) as [[] | ].
trivial.
subst. apply lt_irrefl in l; elim l. elim ( lt_asym v i); trivial.
subst. rewrite plus_comm in l. elim (lt_irrefl i). induction j; simpl in *; intuition.
elim (lt_irrefl i). apply le_lt_trans with v;intuition. rewrite plus_comm in l1; intuition.  
induction j; simpl in *; intuition.
subst. elim (lt_irrefl i). apply lt_trans with (S (i+j)); intuition.
elim (lt_irrefl i). apply lt_trans with (S (i+j)); intuition. apply lt_trans with v; trivial.
simpl. subst. destruct (lt_eq_lt_dec i i) as [[] | ].
elim (lt_irrefl i); trivial. apply substP2; intuition.
elim (lt_irrefl i); trivial.
subst. rewrite plus_comm in e0. apply succ_plus_discr in e0. elim e0.
subst. elim (lt_irrefl i). apply le_lt_trans with (i+j); intuition.
simpl.
destruct (lt_eq_lt_dec (v-1) (i+j)) as  [[] | ]. destruct (lt_eq_lt_dec v i) as [[] | ].
elim (lt_asym v i); trivial. subst. elim (lt_irrefl i); trivial.
trivial. rewrite <- e in l0. rewrite <- pred_of_minus in l0.
rewrite <- (S_pred  v i l) in l0. elim (lt_irrefl v); trivial.
apply lt_n_S in l1. elim (lt_irrefl v).
apply lt_trans with (S(i+j)); trivial.
rewrite <- pred_of_minus in l1. rewrite <- (S_pred  v i l) in l1. trivial. 
subst. simpl. rewrite <- minus_n_O.
destruct (lt_eq_lt_dec (i+j) (i+j)) as [[] | ].
elim (lt_irrefl (i+j)) ; trivial.
symmetry. apply substP3; intuition.
elim (lt_irrefl (i+j)) ; trivial.
simpl.
destruct (lt_eq_lt_dec (v-1) (i+j)) as  [[] | ].
elim (lt_irrefl v). apply lt_trans with (S (i+j)) ;trivial.
apply lt_n_S in l1. rewrite <- pred_of_minus in l1. rewrite <- (S_pred v i l) in l1. trivial.
apply eq_S in e. rewrite <- pred_of_minus in e. rewrite <- (S_pred v i l) in e.
subst. elim (lt_irrefl (S(i+j))); trivial.
destruct (lt_eq_lt_dec (v-1) i) as [[] | ].
elim (lt_irrefl v). apply le_lt_trans with i; trivial. destruct v. apply lt_n_O in l; elim l.
rewrite <- pred_of_minus in l2. simpl in l2. trivial.
destruct v. elim (lt_n_O i); trivial. rewrite <- pred_of_minus in e. simpl in e. subst.
rewrite <- pred_of_minus in l1. simpl in l1. elim (lt_irrefl i).
apply le_lt_trans with (i+j); intuition.
trivial.
Admitted.

Lemma subst_travers : (forall  M N P n, (M [←  N]) [n ←  P] = (M [n+1 ←  P])[←  N[n← P]])/\
                      (forall  H N P n, (H [←h N]) [n ←h P] = (H [n+1 ←h P])[←h N[n← P]]).
destruct substP4;split;intros;simpl;rewrite plus_comm;
change (1+n) with (S n); change n with (0+n); intuition.
Qed.

(** The following two lemmas will be useful for the erasure operation defined later. *)
Lemma erasure_lem1 : (forall a n, a = (a ↑  1 # (S n)) [n ←  #0])/\
                     (forall H n, H = (H ↑h 1 # (S n)) [n ←h #0]).
apply Term_induc;intros;
[unfold lift_rec;destruct le_gt_dec;unfold subst_rec;destruct lt_eq_lt_dec as [[]|];simpl;subst;
try rewrite <- minus_n_O;try rewrite <- plus_n_O;try trivial; elim (lt_irrefl v);simpl in *
|simpl;try rewrite <- H;try rewrite <- H0;try rewrite <- H1;trivial..].
apply lt_trans with (S v);try apply lt_n_Sn; apply lt_trans with n;assumption.
apply lt_trans with (S v);try assumption;apply lt_n_Sn.
apply le_lt_trans with n;try assumption; apply gt_S_le;exact g.
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

(** Here some more lemmas about a lift or substitution being equal to a lifted term*)
Lemma lift_is_lift_sublemma : forall j v, j<v->exists w,#v=w↑1#j.
intros. exists #(v-1). assert (S(v-1)=v). 
rewrite (minus_Sn_m v 1);[simpl;rewrite <- (minus_n_O v);reflexivity|
  unfold lt in H;apply le_trans with (S j);[apply le_n_S;apply le_0_n|assumption]].
simpl;destruct le_gt_dec. rewrite H0;trivial. 
destruct lt_irrefl with j;unfold gt in g;unfold lt in g. rewrite H0 in g. apply lt_le_trans with v;assumption.
Qed.


Lemma lift_is_lift : (forall N A n i j,N ↑  i # n=A ↑  1 # j -> j<n -> exists M,N=M ↑  1 # j)/\
                     (forall N A n i j,N ↑h i # n=A ↑h 1 # j -> j<n -> exists M,N=M ↑h 1 # j).
apply Term_induc;intros;
[|simpl in *;destruct A;simpl in *;try destruct le_gt_dec;try discriminate;
match goal with 
| Heq : _ = _ |- _ => injection Heq;intros;clear Heq
end;
repeat match goal with 
| IH : _ -> _ |- _ => edestruct IH;[eassumption|try apply lt_n_S;assumption|];clear IH
end;subst;
try match goal with 
| |- exists _, ?f _     = _ => eexists (f _    );simpl;reflexivity
| |- exists _, ?f _ _   = _ => eexists (f _ _  );simpl;reflexivity
| |- exists _, ?f _ _ _ = _ => eexists (f _ _ _);simpl;reflexivity
end
..].
simpl in *;destruct le_gt_dec.
apply lift_is_lift_sublemma. apply lt_le_trans with n;assumption.
econstructor;eassumption.
Admitted.

Lemma subst_is_lift : (forall N T A n j, N [n ←  T]=A↑ 1#j->j<n->exists M,N=M↑ 1#j)/\
                      (forall N T A n j, N [n ←h T]=A↑h1#j->j<n->exists M,N=M↑h1#j).
apply Term_induc;intros;
[|simpl in *;destruct A;simpl in *;try destruct le_gt_dec;try discriminate;
match goal with 
| Heq : _ = _ |- _ => injection Heq;intros;clear Heq
end;
repeat match goal with 
| IH : _ -> _ |- _ => edestruct IH;[eassumption|try apply lt_n_S;assumption|];clear IH
end;subst;
try match goal with 
| |- exists _, ?f _     = _ => eexists (f _    );simpl;reflexivity
| |- exists _, ?f _ _   = _ => eexists (f _ _  );simpl;reflexivity
| |- exists _, ?f _ _ _ = _ => eexists (f _ _ _);simpl;reflexivity
end
..].
unfold subst_rec in H;destruct lt_eq_lt_dec as [[]|];[exists A;assumption|apply lift_is_lift_sublemma..].
subst;assumption.
apply lt_trans with n;assumption.
Admitted.


End f_term_mod.
