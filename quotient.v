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

Module Truncation.

  Local Inductive trunc (n : hlevel) (A : Type) : Type :=
  | tr : A -> trunc n A.
  Axiom alpha : forall (n : hlevel) (A : Type) (x y : trunc n A), heq x y.

  (*Definition trunc_rect (n : hlevel) (A B : Type) { h : ishProp B }
                        (f : trunc n A -> B) : trunc n A -> B :=
    trunc_rect n A f.*)

  Axiom _trunc_rect : forall  (n : hlevel) (A B : Type) { h : ishProp B }
        (f : trunc n A -> B), trunc n A -> B.

End Truncation.
Import Truncation.

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

Require Eqdep_dec.

Section MyEqdepDec.

  Variable A : Type.

  Let comp (x y y' : A) (eq1 : heq x y) (eq2 : heq x y') : heq y y'.
  Proof.
    induction eq1.
    exact eq2.
  Defined.

  (*Let comp (A : Type) (x y y' : A) (eq1 : heq x y) (eq2 : heq x y') : heq y y' :=
    heq_ind _ (fun a => heq a y') eq2 _ eq1.*)

  Remark trans_sym_eq : forall (x y : A) (u : heq x y), comp _ _ _ u u = heq_refl y.
  Proof.
    intros x y u.
    now induction u.
  Defined.

  (*Definition trans_sym_eq (A : Type) :=
  let comp :=
      fun (x y y' : A) (eq1 : heq x y) (eq2 : heq x y') =>
        heq_ind _ x (fun a : A => heq a y') eq2 y eq1 in
  fun (x y : A) (u : heq x y) =>
    match u as e in (heq _ y0) return (heq (comp x y0 y0 e e) heq_refl) with
      | heq_refl _ => heq_refl
    end.*)

  Variable x : A.

  Inductive hsum (A : Type) (B : Type) :=
  | inl : forall a : A, hsum A B
  | inr : forall b : B, hsum A B.

  Variable eq_dec : forall y : A, hsum (heq x y) ((heq x y) -> False).

  Let nu (y : A) (u : heq x y) : heq x y :=
    match eq_dec y with
      | inl _ _ eqxy => eqxy
      | inr _ _ neqxy => False_ind _ (neqxy u)
    end.

  Definition nu_left_inv_on (A : Type) :=
    let comp :=
        fun (x y y' : A) (eq1 : heq x y) (eq2 : heq x y') =>
          heq_ind x (fun a : A => heq a y') eq2 y eq1 in
    fun (x : A) (eq_dec : forall y : A, heq x y \/  ~ (heq x y)) =>
      let nu :=
          fun (y : A) (u : heq x y) =>
            match eq_dec y with
              | or_introl eqxy => eqxy
              | or_intror neqxy => False_ind (heq x y) (neqxy u)
            end in
      let nu_inv := fun (y : A) (v : heq x y) => comp x x y (nu x heq_refl) v in
      fun (y : A) (u : heq x y) =>
        match u as e in (heq _ y0) return (heq (nu_inv y0 (nu y0 e)) e) with
          | heq_refl => trans_sym_eq (nu x heq_refl)
        end.

Definition eq_proofs_unicity_on (A : Type) :=
  let comp :=
      fun (x y y' : A) (eq1 : heq x y) (eq2 : heq x y') =>
        eq_ind x (fun a : A => heq a y') eq2 y eq1 in
  fun (x : A) (eq_dec : forall y : A, heq x y \/  ~ (heq x y)) =>
    let nu :=
        fun (y : A) (u : heq x y) =>
          match eq_dec y with
          | or_introl eqxy => eqxy
          | or_intror neqxy => False_ind (heq x y) (neqxy u)
          end in
    let nu_constant :=
        fun (y : A) (u v : heq x y) =>
          let o := eq_dec y in
          match
            o as o0
            return
            (match o0 with
               | or_introl eqxy => eqxy
               | or_intror neqxy => False_ind (heq x y) (neqxy u)
             end =
             match o0 with
               | or_introl eqxy => eqxy
               | or_intror neqxy => False_ind (heq x y) (neqxy v)
             end)
          with
            | or_introl Heq => eq_refl
            | or_intror Hneq =>
              match
                Hneq u as f return (False_ind (heq x y) f = False_ind (heq x y) (Hneq v))
              with
              end
          end in
    let nu_inv := fun (y : A) (v : heq x y) => comp x x y (nu x heq_refl) v in
    fun (y : A) (p1 p2 : x = y) =>
      heq_ind (nu_inv y (nu y p1)) (fun p3 : heq x y => heq p3 p2)
             (heq_ind (nu_inv y (nu y p2)) (fun p3 : heq x y => heq (nu_inv y (nu y p1)) p3)
                     (heq_ind (nu y p1) (fun e : heq x y => heq (nu_inv y (nu y p1)) (nu_inv y e))
                             heq_refl (nu y p2) (nu_constant y p1 p2)) p2
                     (nu_left_inv_on eq_dec p2)) p1
             (nu_left_inv_on eq_dec p1).

Definition eq_proofs_unicity (A : Type) (eq_dec : forall x y : A, heq x y \/  ~ (heq x y)) (x : A) :=
  eq_proofs_unicity_on (eq_dec x).

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
  - apply Eqdep_dec.eq_proofs_unicity.
    intros x y.
    destruct (Z.eq_dec x y).
    + now left.
    + now right.
  - subst.
    exists (heq_refl (diff_even n m k f)).
    intro p.
    
Admitted.

Definition R2Z (n m : Z) : hProp := exist _ (R2Ztype n m) (R2ZhProp n m ).

Definition Z2 := Z // R2Z.


