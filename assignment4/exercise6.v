Variables A: Set.
Variables P Q: A -> Prop.
Theorem exercise6:
    (exists x, (~P x \/ Q x)) -> (exists x,(~(P x /\ ~Q x))).
Proof.
  unfold not.
  intros.
  destruct H as [a p].
  exists a.
  intros.
  destruct H as [H1 H2].
  destruct p as [p1 | p2].
  apply p1.
  apply H1.
  apply H2.
  apply p2.
Qed.