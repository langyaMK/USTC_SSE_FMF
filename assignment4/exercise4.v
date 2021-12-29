Variables A: Set.
Variables P Q: A -> Prop.
Theorem exercise4:
    (forall x, P x -> Q x) -> (forall x, ~Q x) -> (forall x, ~P x).
Proof.
    unfold not.
    intros H1 H2 a H3.
    apply H1 in H3.
    apply H2 in H3.
    apply H3.
Qed.
