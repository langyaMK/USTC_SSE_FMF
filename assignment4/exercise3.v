Variables A: Set.
Variables P Q: A -> Prop.
Theorem exercise3:
    (forall x, ~P x /\ Q x) -> (forall x, P x -> Q x).
Proof.
    intros H1 a H2.
    apply H1.
Qed.