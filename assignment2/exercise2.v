Theorem exercise2: forall P Q H: Prop,
    (P->Q) -> (Q->H) -> (P->H).
Proof.
    intros.
    apply H0 in H2.
    apply H1 in H2.
    apply H2.
Qed.