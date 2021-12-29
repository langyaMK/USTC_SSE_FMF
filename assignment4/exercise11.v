Variables A: Set.
Variables P Q: A -> Prop.
Theorem exercise11:
  (forall x, (P x -> Q x)) /\ (exists x, P x) -> (exists x, Q x).
Proof.
  intros.
  destruct H as [Ha Hb].
  destruct Hb as [a p1].
  apply Ha in p1.
  exists a.
  apply p1.
Qed.