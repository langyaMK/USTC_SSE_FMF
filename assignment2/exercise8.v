Theorem exercise8: forall P Q R: Prop,
    (P /\ Q -> R) <-> (P -> Q -> R).
Proof.
    split.
    intros.
    apply H.
    split.
    apply H0.
    apply H1.
    intros.
    apply H.
    apply H0.
    apply H0.
Qed.