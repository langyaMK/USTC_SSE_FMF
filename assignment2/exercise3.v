Theorem exercise3: forall P Q: Prop,
    P /\ (P -> Q) -> Q.
Proof.
    intros.
    inversion H.
    apply H1 in H0.
    apply H0.
Qed.