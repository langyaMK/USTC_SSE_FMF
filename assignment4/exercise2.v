Theorem example3 : forall P Q R: Prop,
     P /\ (Q \/ R) <-> (P /\ Q) \/ (P /\ R).
Proof.
  split.
  intros.
  destruct H as [Ha Hb].
  destruct Hb as [Hc|Hd].
  left.
  split.
  apply Ha.
  apply Hc.
  right.
  split.
  apply Ha.
  apply Hd.
  intros.
  destruct H as [He | Hf].
  destruct He as [Hg Hh].
  split.
  apply Hg.
  left.
  apply Hh.
  destruct Hf as[Hi Hj].
  split.
  apply Hi.
  right.
  apply Hj.
Qed.