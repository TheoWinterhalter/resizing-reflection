(** *Typing rules for PTSF.*)
Require Import f_term f_env f_typ f_typ2 rr_term rr_env.
Require Import ut_term ut_red ut_env ut_typ ut_sr ut_typ_eq.
Require Import base.
Require Import List.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt Le Gt Plus Minus.

Module f_typ_mod (X : term_sig) (Y : pts_sig X) (FTM : f_term_mod X)
                 (FEM : f_env_mod X FTM)
                 (UTM : ut_term_mod X) (UEM : ut_env_mod X UTM)
                 (URM : ut_red_mod X UTM) (PTS : ut_sr_mod X Y UTM UEM URM)
                 (RE : resizing_env X Y FTM FEM) (TM : rr_term_mod X Y FTM FEM RE)
                 (EM : rr_env_mod X Y FTM FEM RE TM).
  Import X Y FTM FEM TM EM.
  (* Include (f_typ_mod X Y FTM FEM). *)
  (* Include (f_typ2_mod  X Y FTM FEM UTM URM UEM PTS). *)

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
  | cRRAA   : forall Γ n, trunc n Γ ΓΓΓ -> Γ ⊣ -> Γ ⊢ RRAA : ! (RE.t)
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

  Hint Constructors wf typ typ_h.

  Open Scope RR_scope.

  Scheme typ_ind'  := Induction for typ   Sort Prop
  with   wf_ind'   := Induction for wf    Sort Prop
  with   typh_ind' := Induction for typ_h Sort Prop.

  Combined Scheme typ_induc from typ_ind', typh_ind', wf_ind'.

  (** some simple rewrite rules, if the statement P is an conjunction*)
  Ltac rewrite_l P := rewrite ((and_ind (fun A _ => A)) P).
  Ltac rewrite_r P := rewrite ((and_ind (fun _ A => A)) P).
  Ltac rewrite_l_rev P := rewrite <- ((and_ind (fun A _ => A)) P).
  Ltac rewrite_r_rev P := rewrite <- ((and_ind (fun _ A => A)) P).

  Definition semitype A Γ := (exists s,A=!s)\/(exists s, Γ ⊢ A : !s).
  Definition has_type A Γ := (exists B, Γ ⊢ A : B).
  Definition is_type  A Γ := (exists B, Γ ⊢ B : A).
  Definition typ_h_short Γ A B := (exists H, Γ ⊢ H : A = B).
  Notation "Γ ⊢ M = N" := (typ_h_short Γ M N)
                         (at level 80, M, N at level 30, no associativity).
  Notation "Γ ⊢ A : B : C" := (Γ ⊢ A : B/\Γ ⊢ B : C)
                             (at level 80, A, B, C at level 30, no associativity).

  (** Basic properties of PTS.
  Context Validity: if a judgment is valid, its context is well-formed.*)
  Lemma wf_typ : forall Γ t T, Γ ⊢ t : T -> Γ ⊣.
    induction 1; eauto.
  Qed.

  Theorem weakening: 
    (forall Γ M N, Γ ⊢ M : N ->
     forall Δ A s n Γ', ins_in_env Δ A n Γ Γ' -> Δ ⊢ A : !s ->
       Γ' ⊢ M ↑ 1 # n : N ↑ 1 # n ) /\
    (forall Γ H M N, Γ ⊢ H : M = N ->
     forall Δ A s n Γ', ins_in_env Δ A n Γ Γ' -> Δ ⊢ A : !s ->
       Γ' ⊢ H ↑h 1 # n : M ↑ 1 # n = N ↑ 1 # n ) /\
    (forall Γ, Γ ⊣ -> forall Δ A s n Γ', ins_in_env Δ A n Γ Γ' -> Δ ⊢ A : !s -> Γ' ⊣).
  Admitted.

  Theorem thinning : forall Γ M N A s, Γ ⊢ M : N -> Γ ⊢ A : !s -> A::Γ ⊢ M ↑ 1 : N ↑ 1.
    intros ; eapply weakening ; eassumption || econstructor.
  Qed.

  (* First we define a transport that would come in handy. *)

  Open Scope F.

    (* Axiom transport : Sorts -> FTM.Term -> FTM.Term -> FTM.Term -> FTM.Term. *)

    (* DAMN! Is it possible to talk about typing in the other system???!! *)
    (* Axiom transport_typ : *)
    (*   forall (Γ : FEM.Env) (s t : Sorts) (A A' p : FTM.Term), *)
    (*     Ax s t -> *)
    (*     Rel t t t -> *)
    (*     Rel s s s -> *)
    (*     Rel t s t -> *)
    (*     (f_typ_mod X Y FTM FEM).typ Γ A !s -> *)
    (*     Γ ⊢ A  : !s -> *)
    (*     Γ ⊢ A' : !s -> *)
    (*     Γ ⊢ p  : Id !s A A' -> *)
    (*     Γ ⊢ transport s A A' p : Π(A), A' ↑ 1. *)

    (* Maybe we can hope for a version that doesn't need the types. *)
    Axiom transport : FTM.Term -> FTM.Term.
    Notation "p ⋆" := (transport p) (at level 3).

  Close Scope F.

  (* Let's start the translation to PTSf *)

  Reserved Notation "⦑ A ⦒τ" (at level 7, no associativity).
  Reserved Notation "⦑ H ⦒α" (at level 7, no associativity).

  (* We need to have some information about the type if we want to *)
  (* be able to make the transport or proofs such as Rfl... *)
  Fixpoint unrrt (t : Term) : FTM.Term :=
    match t with
    | #v            => (#v)%F
    | !s            => (!s)%F
    | Π(A), B       => (Π (⦑ A ⦒τ), ⦑ B ⦒τ)%F
    | λ[A], t       => (λ[⦑ A ⦒τ], ⦑ t ⦒τ)%F
    | a · b         => (⦑ a ⦒τ · ⦑ b ⦒τ)%F
    | Id A u v      => FTM.Id ⦑A⦒τ ⦑u⦒τ ⦑v⦒τ
    | Rfl A u       => FTM.Rfl ⦑A⦒τ ⦑u⦒τ
    | J A C b u v p => FTM.J ⦑A⦒τ ⦑C⦒τ ⦑b⦒τ ⦑u⦒τ ⦑v⦒τ ⦑p⦒τ
    | t ∽ H         => (⦑H⦒α ⋆ · ⦑t⦒τ)%F
    | RRAA          => RE.BB
    | Inj t         => (RE.ff · ⦑t⦒τ)%F
    | Proj t        => (RE.gg · ⦑t⦒τ)%F
    end
    where "⦑ A ⦒τ" := (unrrt A)
  with unrrp (H : Prf) : FTM.Term :=
    match H with
    | ρ A => FTM.Rfl (#0)%F ⦑A⦒τ
    (* | H †                           => match unrrtp t H with *)
    (*                                   | (t,H) => (t,H †)%F *)
    (*                                   end *)
    (* | H1 • H2                       => match unrrtp t H1 with *)
    (*                                   | (t,H) => unrrtp (t ∽ H)%F H2 *)
    (*                                   end *)
    (* | β A                           => (t, β ⦑A⦒τ)%F *)
    (* | { H1, [A] H2 } => ??? *)
    (* | ⟨ H1, [A] H2 ⟩  => ??? *)
    (* | H1 ·h H2       => ??? *)
    (* Maybe in the three cases above we should do the translation with Refl instead of each Hi *)
    (* | ι (a ∽ H)       => ??? *)
    (* | ι A                           => (#0, FTM.Refl #0)%F *) (* This shouldn't happen so... wildcard *)
    (* | IdEq HA Hu Hv  => ??? *)
    (* | RflEq HA Hu    => ??? *)
    (* | JEq HA HC Hb Hu Hv Hp => ??? *)
    (* | JRed (J A C b u v (Rfl B w)) => (t, FTM.JRed (FTM.J ⦑A⦒τ ⦑C⦒τ ⦑b⦒τ ⦑u⦒τ ⦑v⦒τ (FTM.Rfl ⦑B⦒τ ⦑w⦒τ))) *)
    (* | PI a                         =>  *)
    | H => (#0)%F
    end
    where "⦑ H ⦒α" := (unrrp H).

  Notation "⦑ A ⦒τ" := (unrrt A) (at level 7, no associativity).
  Notation "⦑ H ⦒α" := (unrrp H) (at level 7, no associativity).

  Definition unrrenv (Γ : Env) : FEM.Env :=
    map unrrt Γ.
  Notation "⦑ Γ ⦒γ" := (unrrenv Γ) (at level 7, no associativity).

  Theorem trans_compat :
    (forall Γ t T, Γ ⊢ t : T -> (⦑Γ⦒γ ⊢ ⦑t⦒τ : ⦑T⦒τ)%F) /\
    (forall Γ H A B, Γ ⊢ H : A = B -> exists s, (⦑Γ⦒γ ⊢ ⦑H⦒α : FTM.Id !s ⦑A⦒τ ⦑B⦒τ)%F).


End f_typ_mod.




