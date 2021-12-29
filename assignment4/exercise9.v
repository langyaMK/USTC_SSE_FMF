Variables A: Set.
Variables P: A -> Prop.
Theorem exercise9:
  (exists x, ~P x ) -> ~(forall x, P x).
Proof.
  unfold not.
  intros.
  destruct H as [a p1].
  apply p1.
  apply H0.
Qed.