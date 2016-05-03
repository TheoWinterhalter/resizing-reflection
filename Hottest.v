Require Import HoTT.

Goal forall (A B : Type) (h : IsHSet B) (f : A -> B) (fs : IsSurjection f), { g : B -> A | IsEmbedding g }.
Proof.
  intros A B h f fs.
  refine (exist _ (fun b => _) _).
  - destruct (fs b).
    (* Maybe it isn't possible (at least not in the general case) *)
Abort.

Definition f : S1 -> True.
  intro. exact tt.
Defined.

Goal IsEmbedding f.
Proof.
  intro b. destruct b.
  intros x y. destruct x as [a p]. destruct y as [b q].
  

