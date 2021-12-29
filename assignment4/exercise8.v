Variables A: Set.
Variables P Q: A -> Prop.
Theorem exercise8:
  (exists x, P x \/ Q x) <-> (exists x, P x) \/(exists x, Q x).
Proof.
  split.
  intros.
  destruct H as [a p1].
  destruct p1 as [p2|p3].
  left.
  exists a.
  apply p2.
  right.
  exists a.
  apply p3.
  intros.
  destruct H as [H1 | H2].
  destruct H1 as [a p1].
  exists a.
  left.
  apply p1.
  destruct H2 as [a p2].
  exists a.
  right.
  apply p2.
Qed.