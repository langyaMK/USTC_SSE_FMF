Variables A: Set.
Variables P Q R: A -> Prop.
Theorem exercise12:
  (exists x, (P x /\ Q x)) /\ (forall x, (P x -> R x)) -> (exists x, (R x /\ Q x)).
Proof.
  intros.
  destruct H as [Ha Hb].
  destruct Ha as [a p1].
  destruct p1 as [p2 p3].
  apply Hb in p2.
  exists a.
  split.
  apply p2.
  apply p3.
Qed.