Variables A: Set.
Variables P Q: A -> Prop.
Theorem exercise5:
    (forall x, (P x /\ Q x)) <-> ((forall x, P x) /\ (forall x, Q x)).
Proof.
    split.
    intros.
    split.
    apply H.
    apply H.
    intros H a.
    inversion H.
    split.
    apply H0.
    apply H1.
Qed.