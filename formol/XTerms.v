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
| Refl  : Term -> Prf
| Sym   : Prf  -> Prf
| Trans : Prf  -> Prf  -> Prf
| Beta  : Term -> Term -> Term -> Prf
(* | What's next? *)
.

Notation "! s" := (Sort s) (at level 1) : X_scope.
Notation "# v" := (Var v) (at level 1) : X_scope.
Notation "'Π' ( U ) , V" := (Prod U V)
                           (at level 20, U, V at level 30) : X_scope.
Notation "'λ' [ U ] , v" := (Abs U v)
                           (at level 20, U , v at level 30) : X_scope.
Notation "x · y" := (App x y) (at level 15, left associativity) : X_scope.

