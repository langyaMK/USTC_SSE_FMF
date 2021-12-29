Theorem exercise9: forall P Q R: Prop,
    (P -> Q) -> (~Q -> ~P).
Proof.
    unfold not.
    intros.
    apply H0.
    apply H.
    apply H1.
Qed.