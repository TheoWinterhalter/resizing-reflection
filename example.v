Set Printing Universes.
Set Universe Polymorphism.

(* Contractible types *)

Record contractible (T : Type) :=
  { Point : T ;
    Ctr   : forall t : T, t = Point }.

(* h-levels *)

Inductive hlevel : nat -> Type -> Type :=
| hlevel_O : forall T : Type, contractible T -> hlevel O T
| hlevel_S : forall (m : nat) (T : Type), (forall x y : T, hlevel m (x = y)) -> hlevel (S m) T.

(* h-level 1 : prop *)

Record hProp :=
  { hPropX : Type ;
    hPropP : hlevel 1 hPropX }.

(* h-level 2 : set *)

Record hSet :=
  { hSetX : Type ;
    hSetP : hlevel 2 hSetX }.

(* Resizing rules *)

Axiom rr0@{i j} :
  forall {A : Type@{i}} (B : Type@{j}),
  forall (*{p : eq A B}*) {q : hlevel@{i i i} 1 A@{lol}}, Type@{i}.

(* Axiom rr1 *)

(* We want an example that only works with resizing rules which happens to be
   compact *)

(*Inductive compfun@{i j k} (X : Type@{i}) (R : X -> X -> hProp@{k k k k}) (Y : Type@{j}) :=.*)

Record compfun (X : Type) (R : X -> X -> hProp) (Y : hSet) :=
  { cf : X -> hSetX Y ;
    cp : forall x x' : X, hPropX (R x x') -> cf x = cf x' }.

(*Definition evalfun (X : Type) (R : X -> X -> hProp) :
  X -> forall Y : hSet, compfun X R Y -> hSetX Y
= fun x Y f => cf f x.*)

Definition evalfun@{i}
           (X : Type@{i}) (R : X -> X -> hProp@{i i i i}) (x : X)
           (Y : hSet@{i i i i})
           (f : compfun@{i i i i i i i i i} X R Y) : hSetX@{i i i i} Y =
  cf@{i i i i i i i i i} X R Y f x.






