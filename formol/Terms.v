(** Term definition for our system without extra rules. *)

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
.

Notation "! s" := (Sort s) (at level 1) : T_scope.
Notation "# v" := (Var v) (at level 1) : T_scope.
Notation "'Π' ( U ) , V" := (Prod U V)
                           (at level 20, U, V at level 30) : T_scope.
Notation "'λ' [ U ] , v" := (Abs U v)
                           (at level 20, U , v at level 30) : T_scope.
Notation "x · y" := (App x y) (at level 15, left associativity) : T_scope.

