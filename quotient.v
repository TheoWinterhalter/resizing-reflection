Set Printing Universes.
Set Universe Polymorphism.

(* Polymorhpic equality *)

Inductive heq {A : Type} (x : A) : A -> Type :=
  heq_refl : heq x x.

Notation "A = B" := (heq A B).

(* Sigma *)

Notation idmap := (fun x => x).

Notation compose := (fun g f x => g (f x)).
Notation " g 'o' f " := (compose g f) (at level 40, left associativity)
: core_scope.

Set Primitive Projections.
Record sig {A} (P : A -> Type) := exist { π1 : A ; π2 : P π1 }.
Arguments exist {_} _ _ _.
Scheme sig_rect := Induction for sig Sort Type.

Notation "{ x | P }" := (sig (fun x => P)) (only parsing) : type_scope.
Notation "{ x : A | P }" := (sig (A:=A) (fun x => P)) (only parsing) :
type_scope.
Notation "'exists' x .. y , P"
 := (sig (fun x => .. (sig (fun y => P)) ..))
      (at level 200, x binder, y binder, right associativity) : type_scope.
Notation "∃ x .. y , P"
 := (sig (fun x => .. (sig (fun y => P)) ..))
      (at level 200, x binder, y binder, right associativity) : type_scope.
Notation "( x ; y )" := (exist _ x y) : core_scope.
Notation "( x ; y ; z )" := (x ; (y ; z)) : core_scope.
(* Notation "( x ; y ; .. ; z )" := (exist _ .. (exist _ x y) .. z) :
core_scope. *)
Notation pr1 := (π1 _).
Notation pr2 := (π2 _).
Notation "x .1" := (π1 _ x) (at level 3, format "x '.1'") : core_scope.
Notation "x .2" := (π2 _ x) (at level 3, format "x '.2'") : core_scope.

Definition prod A B := sig (fun _ : A => B).
Notation "A * B" := (prod A B) (at level 40, left associativity) :
type_scope.
Notation "A × B" := (prod A B) (at level 60, right associativity) :
type_scope.
Definition pair {A B} : A -> B -> A × B := fun x y => (x; y).
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
Definition fst {A B} : A × B -> A := pr1.
Definition snd {A B} : A × B -> B := pr2.

Definition iff (A B : Type) := (A -> B) × (B -> A).
Notation "A <-> B" := (iff A B)%type : type_scope.

Definition transitive_iff {A B C}
 : A <-> B -> B <-> C -> A <-> C.
Proof.
 intros H1 H2. split; firstorder.
Defined.

(* Contractible types *)

Record contractible (T : Type) := CtrMk
  { Point : T ;
    Ctr   : forall t : T, heq t Point }.

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
| hctr : forall T : Type@{i}, contractible@{i i} T -> ishType minus2 T
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

Definition hType (n : hlevel) := { T : Type | is-n-Type T }.

Notation "n -Type" := (hType n) (at level 75).

Definition hProp := minus1-Type.
Definition hSet  := 0-Type.

(* Truncation *)

Inductive trunc (n : hlevel) (A : Type) : Type :=
| tr : A -> trunc n A. 
Notation "|| A ||" := (trunc minus1 A).

(* Equivalence *)

Definition comp {A B C} (f : B -> C) (g : A -> B) := fun x => f (g x).
Notation "f ∘ g" := (comp f g) (at level 86).

Definition homo {A B} (f g : A -> B) := forall a : A, f a = g a.
Notation "f ~ g" := (homo f g) (at level 87).

Definition id A := fun x : A => x.

(*Inductive prod A B :=
| pair : forall (a : A) (b : B), prod A B.*)
Notation "A * B" := (prod A B).

Definition isEquiv {A B} (f : A -> B) :=
  { g : B -> A | g ∘ f ~ id A } * { h : B -> A | f ∘ h ~ id B }.

(* Equivalence relations *)

(*Definition pi1 : hProp -> Type.
Proof.
  intro T ; destruct T as [x _] ; exact x.
Defined.*)

Definition pi1 (T : hProp) : Type :=
  let (TT, _) := T in TT.

(* I don't really like this solution with projections but that'll have to do for now. *)
Record isEqRel {A} (R : A -> A -> hProp) :=
  { rho : forall x : A, pi1 (R x x) ;
    sigma : forall x y : A, pi1 (R x y) -> pi1 (R y x) ;
    tau : forall x y z : A, pi1 (R y z) -> pi1 (R x y) -> pi1 (R x z) }.

(* Quotient *)

Definition isEqClass {A} (R : A -> A -> hProp) (P : A -> hProp) :=
  { x : A | forall y : A,  { f : pi1 (R x y) -> pi1 (P y) | isEquiv f } }.

Definition quotient A (R : A -> A -> hProp) := { P : A -> hProp | (trunc minus1 (isEqClass R P)) }.
Notation "A // R" := (quotient A R) (at level 90).

(* Let's try it with Z/2Z *)

Require Import ZArith.

Inductive R2Ztype : Z -> Z -> Type :=
| diff_even : forall n m k, (n - m)%Z = (2 * k)%Z -> R2Ztype n m.

Lemma R2ZhProp : forall n m, ishType minus1 (R2Ztype n m).
Proof.
  intros n m.
  apply hsuc.
  intros x y.
  apply hctr.
  destruct x as [n m k e].
  destruct y as [n m l f].
  assert (l = k) as l_k by omega.
  subst.
  assert (e = f) as e_f.
  - admit.
  - subst.
    exists (heq_refl (diff_even n m k f)).
    intro p.
    admit.
Admitted.

(*Definition R2Z (n m : Z) : hProp.
Proof.
  exists (R2Ztype n m).
  exact (R2ZhProp n m).
Defined.*)

Definition R2Z (n m : Z) : hProp := exist _ (R2Ztype n m) (R2ZhProp n m ).

Definition Z2 := Z // R2Z.

