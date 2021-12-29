Theorem exercise6: forall P Q R: Prop,
    ((P -> R) /\ (Q -> R)) -> (P /\ Q -> R).
Proof.
    intros.
    inversion H.
    inversion H0.
    apply H1 in H3.
    apply H3.
Qed.