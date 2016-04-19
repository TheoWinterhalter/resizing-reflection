Section russell.

  Variable set : Set.
  Variable name : Set -> set.
  Variable El : set -> Set.
  Axiom reflect : forall A:Set, A = El (name A).

  Inductive Tree : Set :=
    span : forall a : set, (El a -> Tree) -> Tree.

  Definition elem (t : Tree) (u : Tree) : Prop
    := match u with
        | span A us => exists a : El A , t = us a
      end.

  Definition Bad (t : Tree) : Prop
    := elem t t.

  Lemma is_good : forall t, ~Bad t.
    induction t; intros [x ex].
    unfold not in H; apply (H x).
    rewrite <- ex.
    exists x; trivial.
  Qed.

  Definition tree := name Tree.

  Definition getTreeAux : forall A : Set, Tree = A -> A -> Tree.
    intros A e a; rewrite e; exact a.
  Defined.

  Definition getAuxTree : forall A : Set, Tree = A -> Tree -> A.
    intros A e a; rewrite <- e; exact a.
  Defined.

  Definition getTree : El tree -> Tree :=
    fun e => (getTreeAux _ (reflect _ ) e).

  Definition Russell := (span _ getTree).

  Lemma is_bad : (Bad Russell).
    exists (getAuxTree _ (reflect _) Russell).
    unfold getTree.
    case (reflect Tree).
    trivial.
  Qed.

  Definition paradox : False := (is_good _ is_bad).

End russell.