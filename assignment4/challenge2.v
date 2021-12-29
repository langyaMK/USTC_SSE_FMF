Variables A: Set.
Variables P: A -> Prop.
Variables b: A.
Theorem Challenge2:
    (P b) /\ (forall (x:A) (y:A), (P x /\ P y -> x = y)) -> (forall (x:A), (P x <-> x = b)).
Proof.
    intros.
    split.
    inversion H.
    intros.
    apply H1.
    split.
    apply H2.
    apply H0.
    intros.
    inversion H.
    rewrite H0.
    apply H1.
Qed.