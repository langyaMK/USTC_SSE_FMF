Theorem exercise7: forall P Q R: Prop,
    (P -> Q /\ R) -> ((P -> Q) /\ (P -> R)).
Proof.
    intros.
    split.
    intros.
    apply H in H0.
    apply H0.
    intros.
    apply H in H0.
    apply H0.
Qed.