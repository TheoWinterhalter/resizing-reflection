Set Printing Universes.
Set Universe Polymorphism.

(* Contractible types *)

Record contractible (T : Type) := CtrMk
  { Point : T ;
    Ctr   : forall t : T, t = Point }.

(* Polymorhpic equality *)

Inductive heq {A : Type} (x : A) : A -> Type :=
  heq_refl : heq x x.

Notation "A = B" := (heq A B).


(* Integers for h-levels *)

Inductive hlevel :=
| minus2 : hlevel
| suc    : hlevel -> hlevel.

Definition minus1 := suc minus2.
Definition zero   := suc minus1.

Notation "-2" := (minus2).
Notation "-1" := (minus1).
Notation "0"  := (zero).

(* is-n-Type *)

Inductive ishType@{i j} : hlevel -> Type@{i} -> Type@{j} :=
| hctr : forall T : Type@{i}, contractible T -> ishType minus2 T
| hsuc : forall (l : hlevel) (T : Type@{i}),
           (forall x y : T, ishType l (heq@{i i} x y)) ->
           ishType (suc l) T.

Notation "is- N -Type" := (ishType N) (at level 80).

Goal is-minus2-Type True.
Proof.
  apply hctr.
  exists I.
  intro t ; now destruct t.
Qed.

Definition ishProp := is-minus1-Type.
Definition ishSet  := is-0-Type.

(* n-Type *)

Definition hType (n : hlevel) := { T : Type & is-n-Type T }.

Notation "n -Type" := (hType n) (at level 75).

Definition hProp := minus1-Type.
Definition hSet  := 0-Type.






