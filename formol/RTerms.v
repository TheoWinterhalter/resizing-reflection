(** Term definition for our system with the resizing. *)

Require Import Base.

(* Implicitely we assume that we have the necessary hypotheses for resizing.
   Namely: an equivalence between A and B in some context.
   We cannot mention them before defining the pure system and its typing,
   and we also need typing rules for the present system to make some sense out
   of it.
   
   Basically, RR represents the resized A that can be seen as a record.
   Inj and Proj correspond to the cannoical injection and projection
   respectively. *)

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
.

Notation "! s" := (Sort s) (at level 1) : R_scope.
Notation "# v" := (Var v) (at level 1) : R_scope.
Notation "'Π' ( U ) , V" := (Prod U V)
                           (at level 20, U, V at level 30) : R_scope.
Notation "'λ' [ U ] , v" := (Abs U v)
                           (at level 20, U , v at level 30) : R_scope.
Notation "x · y" := (App x y) (at level 15, left associativity) : R_scope.

