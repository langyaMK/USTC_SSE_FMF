Theorem exercise5: forall P Q R: Prop,
    (P \/ (Q \/ R)) -> ((P \/ Q) \/ R).
Proof.
    intros.
    inversion H.
    left.
    left.
    apply H0.
    inversion H0.
    left.
    right.
    apply H1.
    right.
    apply H1.
Qed.