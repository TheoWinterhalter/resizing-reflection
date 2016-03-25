Set Printing Universes.
Set Universe Polymorphism.

(* Contractible types *)

Record contractible (T : Type) :=
  { Point : T ;
    Ctr   : forall t : T, t = Point }.

(* h-levels *)

Inductive hlevel@{i j} : nat -> Type@{i} -> Type@{j} :=
| hlevel_O : forall T : Type@{i}, contractible T -> hlevel O T
| hlevel_S : forall (m : nat) (T : Type@{i}),
               (forall x y : T, hlevel m (x = y)) -> hlevel (S m) T.

(* h-level 1 : prop *)

Record hProp@{i j} :=
  { hPropX : Type@{i} ;
    hPropP : hlevel@{i j} 1 hPropX }.

(* h-level 2 : set *)

Record hSet@{i j} :=
  { hSetX : Type@{i} ;
    hSetP : hlevel@{i j} 2 hSetX }.

(* Resizing rules *)

Axiom rr0@{i j si} :
  forall {A : Type@{i}} (B : Type@{j}),
  forall (*{p : eq A B}*) {q : hlevel@{i si} 1 A@{lol}}, Type@{i}.

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






