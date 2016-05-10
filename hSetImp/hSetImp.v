Require Import HoTT.

(* Hurkens Paradox in HoTT *)

Section Hurkens_set_neg.

  Hypothesis funext : Funext.

  Variable p2b : hProp -> Bool.
  Variable b2p : Bool -> hProp.
  Definition dn (A : hProp) := (A -> False) -> False.
  Hypothesis p2p1 : forall A : hProp, dn (b2p (p2b A)) -> dn A.
  Hypothesis p2p2 : forall A : hProp, A -> b2p (p2b A).

  Definition V := forall A : hSet, ((A -> Bool) -> A -> Bool) -> A -> Bool.
  Definition U : hSet. refine (BuildhSet (V -> Bool)). Defined.
  Definition sb (z : V) : V := fun A r a => r (z A r) a.
  Definition le (i : U -> Bool) (x : U) : Bool :=
    x (fun A r a => i (fun v => sb v A r a)).
  Definition induct (i : U -> Bool) : hProp.
    refine (BuildhProp (forall x : U, b2p (le i x) -> dn (b2p (i x)))).
  Defined.
  Definition WF : U := fun z => p2b (induct (z U le)).
  Definition I (x : U) : hProp :=
    (forall i : U -> Bool, b2p (le i x) -> dn (b2p (i (fun v => sb v U le x)))) ->
    False.




