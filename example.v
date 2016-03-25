Set Printing Universes.
Set Universe Polymorphism.

Require Import ZArith.
Open Scope Z_scope.

(* Contractible types *)

Record contractible (T : Type) :=
  { Point : T ;
    Ctr   : forall t : T, t = Point }.

(* h-levels *)

Inductive hlevel@{i j} : Z -> Type@{i} -> Type@{j} :=
| hlevel_0 : forall T : Type@{i}, contractible T -> hlevel (-2) T
| hlevel_S : forall (m : Z) (T : Type@{i}),
               (forall x y : T, hlevel m (x = y)) -> hlevel (m + 1) T.

(* h-level 1 : prop *)

Record hProp@{i j} :=
  { hPropX : Type@{i} ;
    hPropP : hlevel@{i j} (-1) hPropX }.

(* h-level 2 : set *)

Record hSet@{i j} :=
  { hSetX : Type@{i} ;
    hSetP : hlevel@{i j} 0 hSetX }.

(* Resizing rules *)

Inductive eq {A : Type} (x : A) : A -> Type :=
  eq_refl : eq x x.

Definition isEquiv (A : Type) (B : Type) (f : A -> B) :=
  exists g : B -> A, forall a : A, g (f a) = a /\ forall b : B, f (g b) = b.

Record Equiv (A : Type) (B : Type) :=
  { equivf : A -> B ;
    equivp : isEquiv A B equivf }.

Axiom rr0@{i j si} :
  forall {A: Type@{i}} (B : Type@{j}),
  forall {p : Equiv A B} {q : hlevel@{i si} (-1) A}, Type@{i}.

(* Axiom rr1 *)

(* We want an example that only works with resizing rules which happens to be
   compact *)

(*Inductive compfun@{i j k} (X : Type@{i}) (R : X -> X -> hProp@{k k k k}) (Y : Type@{j}) :=.*)

Record compfun@{i si j sj}
       (X : Type@{i}) (R : X -> X -> hProp@{i si}) (Y : hSet@{j sj}) :=
  { cf : X -> hSetX@{j sj} Y ;
    cp : forall x x' : X, hPropX@{j sj} (R x x') -> cf x = cf x' }.

(*Definition evalfun (X : Type) (R : X -> X -> hProp) :
  X -> forall Y : hSet, compfun X R Y -> hSetX Y
:= fun x Y f => cf f x.*)

Definition evalfun@{i si}
           (X : Type@{i}) (R : X -> X -> hProp@{i si}) (x : X)
           (Y : hSet@{i si})
           (f : compfun@{i si i si} X R Y) : hSetX@{i si} Y :=
  cf@{i si i si} X R Y f x.

Record im@{i j} (X : Type@{i}) (Y : Type@{j}) (f : X -> Y) :=
  { im_y : Y ;
    im_x : X ;
    im_p : f im_x = im_y }.

Definition quotient@{i si}
           (X : Type@{i}) (R : X -> X -> hProp@{i si}) :=
  im@{i si}
    X
    (forall Y : hSet@{i si}, compfun@{i si i si} X R Y -> hSetX@{i si} Y)
    (evalfun@{i si} X R).





