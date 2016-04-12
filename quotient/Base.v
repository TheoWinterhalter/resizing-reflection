Set Printing Universes.
Set Universe Polymorphism.

(* Polymorhpic equality *)

Inductive heq {A : Type} (x : A) : A -> Type :=
  heq_refl : heq x x.

Notation "A = B" := (heq A B) (at level 70).

(* Fun Ext *)

Axiom fun_ext : forall {A B} {f g : A -> B}, (forall x, heq (f x) (g x)) -> heq f g.
Axiom dep_fun_ext : forall {A B} {f g : forall a : A, B a}, (forall a, heq (f a) (g a)) -> heq f g.

(* transitivity of heq *)
Lemma heq_trans {A} : forall a b c : A, heq a b -> heq b c -> heq a c.
Proof.
  intros a b c eqab eqbc.
  destruct eqab.
  exact eqbc.
Defined.

Lemma heq_sym {A} : forall a b : A, heq a b -> heq b a.
Proof.
  intros a b eq.
  now destruct eq.
Defined.

Lemma hf_equal : forall {A B : Type} (f : A -> B) {x y : A}, heq x y -> heq (f x) (f y).
Proof.
  intros A B f x y h.
  now destruct h.
Defined.

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