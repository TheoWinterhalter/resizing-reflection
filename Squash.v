Set Universe Polymorphism.

(* Preliminary notations *)
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

(* FunExt *)
Axiom funext : forall {A B} {f g : forall a : A, B a}, (forall a, (f a) = (g a)) -> f = g.

(* hProp *)

Definition ishProp A : Type := forall x y : A, x = y.
Definition hProp := { A | ishProp A }.

(* The squash as a quotient. *)
Definition trunc A := { P : A -> hProp | forall y : A, (P y).1 }.

Lemma trunc_hProp : forall A, ishProp (trunc A).
Proof.
  intros A x y.
  destruct x as [P hP] ; destruct y as [Q hQ].
  assert (P = Q).
  - apply funext. intro a.



