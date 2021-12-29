Variables A: Set.
Variables P Q: A -> Prop.
Theorem exercise10:
  (forall x, (P x -> ~Q x)) -> ~(exists x, (P x /\ Q x)).
Proof.
  unfold not.
  intros.
  destruct H0 as [a p1].
  destruct p1 as [p2 p3].
  apply H in p2.
  apply p2.
  apply p3.
Qed.