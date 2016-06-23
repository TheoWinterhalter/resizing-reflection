(** Term definition for our system with resizing and explicit conversion. *)

Require Import Base.

Inductive Term :=
| Var  : Vars  -> Term
| Sort : Sorts -> Term
| Prod : Term  -> Term -> Term
| Abs  : Term  -> Term -> Term
| App  : Term  -> Term -> Term
| Id   : Term  -> Term -> Term
| Rfl  : Term  -> Term -> Term
| J    : Term  -> Term -> Term -> Term -> Term -> Term -> Term
| RR   : Term
| Inj  : Term  -> Term
| Proj : Term  -> Term
| Conv : Term  -> Prf  -> Term
with Prf :=
| Refl   : Term -> Prf
| Sym    : Prf  -> Prf
| Trans  : Prf  -> Prf  -> Prf
| Beta   : Term -> Term -> Term -> Prf
| ProdEq : Prf  -> Term -> Prf  -> Prf
| AbsEq  : Prf  -> Term -> Prf  -> Prf
| AppEq  : Prf  -> Prf  -> Prf
| IdEq   : Prf  -> Prf  -> Prf  -> Prf
| RflEq  : Prf  -> Prf  -> Prf
| JEq    : Prf  -> Prf  -> Prf  -> Prf  -> Prf -> Prf -> Prf
| JRed   : Term -> Term -> Term -> Term -> Prf
| ConvEq : Prf  -> Prf  -> Prf
.

Notation "! s" := (Sort s) (at level 1) : X_scope.
Notation "# v" := (Var v) (at level 1) : X_scope.
Notation "'Π' ( U ) , V" := (Prod U V)
                           (at level 20, U, V at level 30) : X_scope.
Notation "'λ' [ U ] , v" := (Abs U v)
                           (at level 20, U , v at level 30) : X_scope.
Notation "x · y" := (App x y) (at level 15, left associativity) : X_scope.
Notation "t ∽ H" := (Conv t H) (at level 15) : X_scope.
Notation "'ρ' A" := (Refl A) (at level 6) : X_scope. 
Notation "H †" := (Sym H) (at level 6) : X_scope.
Notation "H1 • H2" := (Trans H1 H2) (at level 15, left associativity) : X_scope.
Notation "'β' A b a" := (Beta A b a) (at level 6) : X_scope.
Notation "{ H1 , [ A ] H2 }" := (ProdEq H1 A H2) (at level 15) : X_scope.
Notation "⟨ H1 , [ A ] H2 ⟩" := (AbsEq H1 A H2)
                              (at level 15, left associativity) : X_scope.
Notation "H1 ·h H2" := (AppEq H1 H2)
                      (at level 15, left associativity) : X_scope.
Notation "H1 ∽h H2" := (ConvEq H1 H2) (at level 15) : X_scope.


