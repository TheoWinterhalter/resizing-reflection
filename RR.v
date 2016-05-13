Set Universe Polymorphism.
Set Primitive Projections.

Inductive eq@{i} {A : Type@{i}} (x : A) : A -> Type@{i} := eq_refl : eq x x.

Definition hProp@{i} (A : Type@{i}) : Type@{i} := forall x y : A, eq x y.

ON Unsafe Universes.

Section Foo.

Universes i j.

Record RR (A : Type@{i}) (H : hProp@{i} A) : Type@{j} := { rr : A }.

End Foo.

OFF Unsafe Universes.

Unset Universe Polymorphism.

Let U := Type.
Let V := let X : U := Type in X.

Fail Check (U : V).
Check (V : U).

Definition inj@{i j} (A : Type@{i}) (h : hProp@{i} A) (x : A) : RR@{i j} A h := Build_RR A h x.
Definition prj@{i j} {A : Type@{i}} {h : hProp@{i} A} (p : RR@{i j} A h) : A := p.(rr _ _).

Print RR.

Section Bar.

Variable A : Type.
Variable H : hProp A.
Variable x : A.

Check (Logic.eq_refl : prj (inj A H x) = x).

End Bar.


(* Let's go for a rule with embedding instead *)

Set Universe Polymorphism.

Notation "A == B" := (eq A B) (at level 50).

Definition ap {A B} (f : A -> B) {x y  : A} (e : eq x y) : eq (f x) (f y) :=
  match e with eq_refl _ => eq_refl _ end.

Record isEquiv {A B} (f : A -> B) :=
  { g : B -> A ;
    eta : forall x : A, g (f x) == x ;
    epsilon : forall y : B, f (g y) == y ;
    alpha : forall x : A, ap f (eta x) == epsilon (f x) }.

Record Embedding A B :=
  { f : A -> B ; e : forall x y : A, isEquiv (@ap A B f x y) }.

ON Unsafe Universes.

Section RREmb.

  Universes i j.

  Record RRe (A : Type@{i}) (B : Type@{j}) (h : Embedding A B) : Type@{j} := { box : A }.

End RREmb.

OFF Unsafe Universes.

Definition lift@{i j} (A : Type@{i}) (B : Type@{j}) (h : Embedding A B) (x : A) : RRe A B h := Build_RRe A B h x.
Definition proj@{i j} {A : Type@{i}} {B : Type@{j}} {h : Embedding A B} (p : RRe A B h) : A := p.(box _ _ _).

Section Checking.
  
  Variables A B : Type.
  Variable h : Embedding A B.
  Variable x : A.
  Variable y : RRe A B h.
  
  Check (eq_refl _ : proj (lift A B h x) == x).
  Check (eq_refl _ : lift A B h (proj y) == y).

End Checking.

Set Printing Universes.
Unset Universe Polymorphism.

Let Uni := Type.
Definition BigUnit : Type := forall T : Uni, T = True -> T.
Fail Check BigUnit : Uni.

Axiom funext : forall A B (f g : forall x : A, B x), (forall x : A, f x == g x) -> f == g.

Lemma small_bigunit : Embedding BigUnit True.
Proof.
  exists (fun _ => I). intros x y.
  simple refine (Build_isEquiv (x == y) ((fun _ => I) x == (fun _ => I) y) (fun e => _) _ _ _ _).
  - intro e. unfold BigUnit in x,y. apply funext. intro z. apply funext. intro t.
    rewrite t. destruct (x True Logic.eq_refl). now destruct (y True Logic.eq_refl).
  - intro e.

