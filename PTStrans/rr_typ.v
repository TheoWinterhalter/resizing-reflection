(** *Typing rules for PTSF.*)
Require Import f_term f_env rr_term rr_env.
Require Import base.
Require Import List.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt Le Gt Plus Minus.

Module f_typ_mod (X : term_sig) (Y : pts_sig X) (FTM : f_term_mod X) (FEM : f_env_mod X FTM)
                 (RE : resizing_env X Y FTM FEM) (TM : rr_term_mod X Y FTM FEM RE)
                 (EM : rr_env_mod X Y FTM FEM RE TM).
  Import X Y TM EM.

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
  | cId     : forall Γ A u v s, Γ ⊢ A : !s -> Γ ⊢ u : A -> Γ ⊢ v : A -> Γ ⊢ Id A u v : !s
  | cRfl    : forall Γ A u s, Γ ⊢ A : !s -> Γ ⊢ u : A -> Γ ⊢ Rfl A u : Id A u u
  | cJ      : forall Γ A C b u v p s t,
                Γ ⊢ A : !s ->
                Γ ⊢ C : Π(A), Π(A ↑ 1), Π(Id (A ↑ 2) #1 #0), !t ->
                Γ ⊢ b : Π(A), (C ↑ 1) · #0 · #0 · (Rfl (A ↑ 1) #0) ->
                Γ ⊢ u : A -> Γ ⊢ v : A -> Γ ⊢ p : Id A u v ->
                Γ ⊢ J A C b u v p : C · u · v · p
  | cConv   : forall Γ a A B s H, Γ ⊢ a : A -> Γ ⊢ B : !s -> Γ ⊢ H : A = B -> Γ ⊢ a ∽ H : B
  | cRRAA   : forall Γ n, trunc n Γ ΓΓΓ -> Γ ⊢ RRAA : ! (RE.t)
  | cInj    : forall Γ t, Γ ⊢ t : AAA -> Γ ⊢ Inj t : RRAA
  | cProj   : forall Γ t, Γ ⊢ t : RRAA -> Γ ⊢ Proj t : AAA
  where "Γ ⊢ t : T" := (typ Γ t T) : RR_scope
  with typ_h : Env -> Prf -> Term -> Term -> Prop :=
  | cRefl   : forall Γ a A, Γ ⊢ a : A -> Γ ⊢ ρ a : a = a
  | cSym    : forall Γ H A B, Γ ⊢ H : A = B -> Γ ⊢ H† : B = A
  | cTrans  : forall Γ H K A B C, Γ ⊢ H : A = B -> Γ ⊢ K : B = C -> Γ ⊢ H•K : A = C
  | cBeta   : forall Γ a A b B s1 s2 s3,
                Rel s1 s2 s3 -> Γ ⊢ a : A -> Γ ⊢ A : !s1 ->
                A::Γ ⊢ b : B -> A::Γ ⊢ B : !s2 -> Γ ⊢ β((λ[A], b)·a) : (λ[A], b)·a = b[←a]
  | cProdEq : forall Γ A A' B B' H K s1 s2 s3 s1' s2' s3',
                Rel s1 s2 s3 -> Rel s1' s2' s3' ->
                Γ ⊢ A : !s1 -> Γ ⊢ A' : !s1' -> A::Γ ⊢ B : !s2 -> A'::Γ ⊢ B' : !s2' ->
                Γ ⊢ H : A = A' -> A::Γ ⊢ K : B = (B'↑1#1)[←#0∽H↑h1] -> Γ ⊢ {H,[A]K} : Π(A), B = Π(A'), B'
  | cAbsEq  : forall Γ A A' b b' B B' H K s1 s2 s3 s1' s2' s3',
                Rel s1 s2 s3 -> Rel s1' s2' s3' ->
                Γ ⊢ A : !s1 -> Γ ⊢ A' : !s1' -> A::Γ ⊢ b : B -> A'::Γ ⊢ b' : B' -> A::Γ ⊢ B : !s2 -> A'::Γ ⊢ B' : !s2' ->
                Γ ⊢ H : A = A' -> A::Γ ⊢ K : b = (b'↑1#1)[←#0∽H↑h1] -> Γ ⊢ ⟨H,[A]K⟩ : λ[A], b = λ[A'], b'
  | cAppEq  : forall Γ F F' a a' A A' B B' H K,
                Γ ⊢ F : Π(A), B -> Γ ⊢ F' : Π(A'), B' -> Γ ⊢ a : A -> Γ ⊢ a' : A' ->
                Γ ⊢ H : F = F' -> Γ ⊢ K : a = a' -> Γ ⊢ H ·h K : F · a = F' · a'
  | cIota   : forall Γ a A B s H, Γ ⊢ a : A -> Γ ⊢ B : !s -> Γ ⊢ H : A = B -> Γ ⊢ ι(a∽H) : a = a∽H
  | cIdEq   : forall Γ A A' u u' v v' s s' HA Hu Hv,
                Γ ⊢ A  : !s     -> Γ ⊢ A' : !s' ->
                Γ ⊢ u  : A      -> Γ ⊢ u' : A'  ->
                Γ ⊢ v  : A      -> Γ ⊢ v' : A'  ->
                Γ ⊢ HA : A = A' ->
                Γ ⊢ Hu : u = u' -> Γ ⊢ Hv : v = v' ->
                Γ ⊢ IdEq HA Hu Hv : Id A u v = Id A' u' v'
  | cRflEq  : forall Γ A A' u u' s s' HA Hu,
                Γ ⊢ A  : !s     -> Γ ⊢ A' : !s'    ->
                Γ ⊢ u  : A      -> Γ ⊢ u' : A'     ->
                Γ ⊢ HA : A = A' -> Γ ⊢ Hu : u = u' ->
                Γ ⊢ RflEq HA Hu : Rfl A u = Rfl A' u'
  | cJEq    : forall Γ A A' C C' b b' u u' v v' p p' s t s' t' HA HC Hb Hu Hv Hp,
                Γ ⊢ A  : !s       -> Γ ⊢ A' : !s'         ->
                Γ ⊢ C  : Π(A), Π(A ↑ 1), Π(Id (A ↑ 2) #1 #0), !t ->
                Γ ⊢ C' : Π(A'), Π(A' ↑ 1), Π(Id (A' ↑ 2) #1 #0), !t' ->
                Γ ⊢ b  : Π(A), (C ↑ 1) · #0 · #0 · (Rfl (A ↑ 1) #0) ->
                Γ ⊢ b' : Π(A'), (C' ↑ 1) · #0 · #0 · (Rfl (A' ↑ 1) #0) ->
                Γ ⊢ u  : A        -> Γ ⊢ u' : A'          ->
                Γ ⊢ v  : A        -> Γ ⊢ v' : A'          ->
                Γ ⊢ p  : Id A u v -> Γ ⊢ p' : Id A' u' v' ->
                Γ ⊢ HA : A = A'   -> Γ ⊢ HC : C = C'      ->
                Γ ⊢ Hb : b = b'   -> Γ ⊢ Hu : u = u'      ->
                Γ ⊢ Hv : v = v'   -> Γ ⊢ Hp : p = p'      ->
                Γ ⊢ JEq HA HC Hb Hu Hv Hp : J A C b u v p = J A' C' b' u' v' p'
  | cJRed   : forall Γ A C b u s t,
                Γ ⊢ A : !s ->
                Γ ⊢ C : Π(A), Π(A ↑ 1), Π(Id (A ↑ 2) #1 #0), !t ->
                Γ ⊢ b : Π(A), (C ↑ 1) · #0 · #0 · (Rfl (A ↑ 1) #0) ->
                Γ ⊢ u : A ->
                Γ ⊢ JRed (J A C b u u (Rfl A u)) : J A C b u u (Rfl A u) = b · u
  | cPI     : forall Γ t,
                Γ ⊢ t : AAA ->
                Γ ⊢ PI t : Proj (Inj t) = t
  | cIP     : forall Γ t,
                Γ ⊢ t : RRAA ->
                Γ ⊢ IP t : Inj (Proj t) = t
  where "Γ ⊢ H : A = B" := (typ_h Γ H A B) : RR_scope.

End f_typ_mod.




