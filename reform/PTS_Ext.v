Require Import List.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt Le Gt.
Require Import Sorts. Import withoutProp.

(** * Term definition for PTS and de Bruijn manipulation . *)
(** * Usual Term syntax .*)

(** Term syntax:*)
Inductive Term : Set :=
| Var : Vars -> Term
| Sort : Sorts -> Term
| Π : Term -> Term -> Term
| λ : Term -> Term -> Term
| App : Term -> Term -> Term
| Eq : forall (A M N : Term), Term
| refle : Term -> Term
| J : forall (A P M1 N M2 p : Term), Term
.

Notation "# v" := (Var v) (at level 1) : UT_scope.
Notation "! s" := (Sort s) (at level 1) : UT_scope.
Notation "x · y" := (App x y) (at level 15, left associativity) : UT_scope.
Delimit Scope UT_scope with UT. 
Open Scope UT_scope.


Reserved Notation " t ↑ x # n " (at level 5, x at level 0, left associativity).


(** In order to deal with variable bindings and captures, we need a lift
function to deal with free and bounded variables.
[M ↑ n # k recursivly add [n] to all variables that are
 above [k] in [M]. *)
Fixpoint lift_rec (n:nat) (k:nat) (T:Term) {struct T}
  := match T with
     | # x =>  if le_gt_dec k x then Var (n+x) else Var x
     | ! s => !s
     | M · N =>  App (M ↑ n # k) (N ↑ n # k)
     | Π  A B => Π  (A ↑ n # k) (B ↑ n # (S k))
     | λ A M => λ (A ↑ n # k) (M ↑ n # (S k)) 
     | Eq A t1 t2 => Eq (A ↑ n # k) (t1 ↑ n # k) (t2 ↑ n # k)
     | refle t => refle (t ↑ n # k)
     | J A P t1 u t2 p => J (A ↑ n # k) (P ↑ n # (S k)) (t1 ↑ n # k)
                           (u ↑ n # k) (t2 ↑ n # k) (p ↑ n # k)
     end  
where "t ↑ n # k" := (lift_rec n k t) : UT_scope.

Notation " t ↑ n " := (lift_rec n 0 t) (at level 5, n at level 0, left associativity) : UT_scope.
Notation " t ↑ " := (lift_rec 1 0 t) (at level 5, left associativity) : UT_scope.

(** We will consider the usual implicit substitution without variable capture
(this is where the lift operator comes in handy).
  [ M [ n ← N ] ] replace the variable [n] in [M] by the term [N].
 *)
Reserved Notation "t [ x ← u ]" (at level 5, x at level 0, left associativity).

Fixpoint subst_rec u t n {struct t} :=
  match t with
  | # x => match (lt_eq_lt_dec x n) with
          | inleft (left _) => # x (* x < n *)
          | inleft (right _) => u ↑ n  (* x = n *)
          | inright _ => # (x - 1) (* x > n *)
          end
  | ! s => ! s
  | M · N => (M [ n ← u ]) · ( N [ n ← u ]) 
  | Π  A B => Π ( A [ n ← u ] ) (B [ S n ← u ]) 
  | λ  A M => λ (A [ n ← u ]) (M [ S n ← u ]) 
  | Eq A t1 t2 => Eq (A [ n ← u ]) (t1 [ n ← u ]) (t2 [ n ← u ])
  | refle t => refle (t [ n ← u ])
  | J A P t1 v t2 p => J (A [ n ← u ]) (P [ S n ← u ]) (t1 [ n ← u ])
                        (v [ n ← u ]) (t2 [ n ← u ]) (p [ n ← u ])
  end
where " t [ n ← u ] " := (subst_rec u t n) : UT_scope.

Notation " t [ ← u ] " := (subst_rec u t 0) (at level 5) : UT_scope.
  
(** Since we use de Bruijn indexes, Environment (or Context) are
simply lists of terms:  Γ(x:A) is encoded as  [A::Γ]. *)

Definition Env := list Term.

Set Implicit Arguments.

Inductive item (A:Type) (x:A): list A -> nat -> Prop :=
| item_hd: forall Γ :list A, (item x (cons x Γ) O)
| item_tl: forall (Γ:list A)(n:nat)(y:A), item x Γ n -> item x (cons y Γ) (S n).

Hint Constructors item.

(** In the list [Γ], the [n]th item is syntacticaly [x]. *)
Notation " x ↓ n ∈ Γ " := (item x Γ n) (at level 80, no associativity) : UT_scope.

(** In the list [Γ], [t] is  [n]th element correctly lifted according to [Γ]:
e.g.: if t ↓ n ⊂ Γ and we insert something in Γ, then 
we can still speak about t without think of the lift hidden by the insertion. *)

Definition item_lift (t:Term) (Γ:Env) (n:nat) :=
  exists u ,  t= u ↑ (S n) /\  u ↓ n ∈ Γ .

Hint Unfold item_lift.
Notation " t ↓ n ⊂ Γ " := (item_lift t Γ n) (at level 80, no associativity): UT_scope.

(** Typing judgements:*)
Reserved Notation "Γ ⊢ t : T" (at level 80, t, T at level 30, no associativity).
Reserved Notation "Γ ⊣ " (at level 80, no associativity).
Reserved Notation "Γ ⊢ u ≡ v"
         (at level 80, u, v at level 30, no associativity).

Notation "A ⇒ B" := (Π A (B ↑)) (at level 20, right associativity).
Definition empty := Π !(U 0) #0.
Notation "⊥" := empty.

Inductive wf : Env -> Prop :=
| wf_nil   : nil ⊣
| wf_cons : forall Γ A s, Γ ⊢ A : !s -> A::Γ ⊣
where "Γ ⊣" := (wf Γ) : UT_scope
with
typ : Env -> Term -> Term -> Prop :=
| cVar   : forall Γ A v              , Γ ⊣ -> A ↓ v  ⊂ Γ -> Γ ⊢ #v : A
| cSort  : forall Γ s s'             , Γ ⊣ -> Ax s s' -> Γ  ⊢ !s : !s'
| cΠ     : forall Γ A B s s' s''     , Rel s s' s'' -> Γ ⊢ A : !s -> A :: Γ ⊢ B : !s' ->
                                  Γ ⊢  Π  A B : !s''
| cλ     : forall Γ A B s s' s'' M   , Rel s s' s'' -> Γ ⊢ A : !s -> A::Γ ⊢ B : !s' ->
                                  A :: Γ ⊢ M : B -> Γ ⊢ λ A M : Π  A B
| cApp   : forall Γ M N A B          , Γ ⊢ M : Π A B -> Γ ⊢ N : A -> Γ ⊢ M · N : B[← N]
| cEq    : forall Γ A t1 t2 s        , Γ ⊢ A : !s -> Γ ⊢ t1 : A -> Γ ⊢ t2 : A ->
                                  Γ ⊢ Eq A t1 t2 : !s
| crefle : forall Γ t A              , Γ ⊢ t : A -> Γ ⊢ refle t : Eq A t t
| cJ     : forall Γ A P t1 u t2 p s  , A :: Γ ⊢ P : !s -> Γ ⊢ u : P[← t1] ->
                                  Γ ⊢ p : Eq A t1 t2 ->
                                  Γ ⊢ J A P t1 u t2 p : P[← t2]
| Cnv    : forall Γ M A B s          , Γ ⊢ A ≡ B -> Γ ⊢ M : A -> Γ ⊢ B : !s -> Γ ⊢ M : B
where "Γ ⊢ t : T" := (typ Γ t T) : UT_scope
with
eq : Env -> Term -> Term -> Prop :=
| eβ     : forall Γ A t u T          , Γ ⊢ (λ A t) · u : T ->
                                  Γ ⊢ (λ A t) · u ≡ t [← u]
| eApp   : forall Γ t1 t2 u1 u2      , Γ ⊢ t1 ≡ t2 -> Γ ⊢ u1 ≡ u2 ->
                                  Γ ⊢ t1 · u1 ≡ t2 · u2
| eΠ     : forall Γ A1 A2 B1 B2      , Γ ⊢ A1 ≡ A2 -> A1 :: Γ ⊢ B1 ≡ B2 ->
                                  Γ ⊢ Π A1 B1 ≡ Π A2 B2
| eλ     : forall Γ A1 A2 t1 t2      , Γ ⊢ A1 ≡ A2 -> A1 :: Γ ⊢ t1 ≡ t2 ->
                                  Γ ⊢ λ A1 t1 ≡ λ A2 t2
| eEq    : forall Γ A1 A2 t1 t2 u1 u2, Γ ⊢ A1 ≡ A2 -> Γ ⊢ t1 ≡ t2 -> Γ ⊢ u1 ≡ u2 ->
                                  Γ ⊢ Eq A1 t1 u1 ≡ Eq A2 t2 u2
| erefle : forall Γ t1 t2            , Γ ⊢ t1 ≡ t2 -> Γ ⊢ refle t1 ≡ refle t2
| eJ     : forall Γ A1 A2 P1 P2 t1 t2 u1 u2 v1 v2 p1 p2,
                                  Γ ⊢ A1 ≡ A2 -> A1 :: Γ ⊢ P1 ≡ P2 -> Γ ⊢ u1 ≡ u2 ->
                                  Γ ⊢ t1 ≡ t2 -> Γ ⊢ v1 ≡ v2 -> Γ ⊢ p1 ≡ p2 ->
                                  Γ ⊢ J A1 P1 t1 u1 v1 p1 ≡ J A2 P2 t2 u2 v2 p2
| eJβ    : forall Γ A P M N          , Γ ⊢ J A P M N M (refle M) ≡ N
(* The only difference is the reflection rule (and the absence of axioms). *)
| eRef   : forall Γ p A u v          , Γ ⊢ p : Eq A u v -> Γ ⊢ u ≡ v
(* Equivalence rules *)
| eRefl  : forall Γ M T, Γ ⊢ M : T -> Γ ⊢ M ≡ M
| eSym   : forall Γ M N, Γ ⊢ M ≡ N -> Γ ⊢ N ≡ M
| eTrans : forall Γ M N U, Γ ⊢ M ≡ N -> Γ ⊢ N ≡ U -> Γ ⊢ M ≡ U
where "Γ ⊢ u ≡ v" := (eq Γ u v) : UT_scope.

Hint Constructors wf typ eq.
Open Scope UT_scope.

Scheme typ_ind' := Induction for typ Sort Prop
with wf_ind' := Induction for wf Sort Prop
with eq_ind' := Induction for eq Sort Prop.
Combined Scheme typ_induc from typ_ind', wf_ind', eq_ind'.

Lemma wf_typ : forall Γ t T, Γ ⊢ t : T -> Γ ⊣.
induction 1; eauto.
Qed.