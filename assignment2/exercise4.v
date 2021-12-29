Theorem exercise4: forall P Q R:Prop,
    (P /\ (Q /\ R)) -> ((P /\ Q) /\ R).
Proof.
    intros.
    inversion H.
    inversion H1.
    split.
    split.
    apply H0.
    apply H2.
    apply H3.
Qed.