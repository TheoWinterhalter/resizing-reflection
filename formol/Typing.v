(** Typing for pure terms. *)

Require Import Base Terms.
Require Import List.

Reserved Notation "Γ ⊢ t : T" (at level 80, t, T at level 30, no associativity).
Reserved Notation "Γ ⊢ t = t' : T" (at level 80,
                                    t, t' , T at level 30,
                                    no associativity).
Reserved Notation "Γ ⊣" (at level 80, no associativity).

Inductive wf : Env -> Type :=
| wf_nil  : nil ⊣
| wf_cons : forall Γ A s, Γ ⊢ A : !s -> A::Γ ⊣
where "Γ ⊣" := (wf Γ) : T_scope
with typ : Env -> Term -> Term -> Type :=
| tSort : forall Γ s t, Ax s t -> Γ ⊣ -> Γ ⊢ !s : !t
(* | tVar  : forall Γ A v, Γ ⊣ -> ... *)
where "Γ ⊢ t : T" := (typ Γ t T) : T_scope
with typ_eq : Env -> Term -> Term -> Term -> Type :=
| cSort : forall Γ s t, Ax s t -> Γ ⊣ -> Γ ⊢ !s = !s : !t
(* | *)
where "Γ ⊢ t = t' : T" := (typ_eq Γ t t' T) : T_scope.

