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
  (* I think we can't conclude, which would be great! *)
Abort.

Goal forall A (h : IsHProp A), { f : A -> True & IsEmbedding f }.
Proof.
  intros A h.
  exists (fun a => tt).
  intro y. destruct y.
  intros x y. destruct x as [x p]. destruct y as [y q].
  assert (x = y) as eqxy.
  - apply h.
  - destruct eqxy.
    assert (p = q) as eqpq.
    + apply hset_decpaths. intros u v. destruct u ; destruct v. left. reflexivity.
    + destruct eqpq. exists idpath. intro y.
      apply hset_decpaths. intros u v. destruct u as [u q] ; destruct v as [v r]. left.
      assert (u = v) as equv.
      * apply h.
      * { assert (q = r) as eqqr.
          - apply hset_decpaths. intros a b. destruct a ; destruct b. left ; reflexivity.
          - destruct equv. destruct eqqr. reflexivity.
        }
Defined.

Goal forall A (f : A -> True), IsEmbedding f -> IsHProp A.
Proof.
  intros A f h x y.
  pose (h tt) as htt.
  assert (f x = tt) as p by (case (f x) ; reflexivity).
  assert (f y = tt) as q by (case (f y) ; reflexivity).
  pose (htt (x ; p) (y ; q)) as hh. destruct hh as [c t].
  assert (x = y) as eqxy.
  - pose (ap projT1 c) as hhh. simpl in hhh. assumption.
  - destruct eqxy. exists idpath. intro r.
    (* I feel like it works but it's hard to see clearly. *)

