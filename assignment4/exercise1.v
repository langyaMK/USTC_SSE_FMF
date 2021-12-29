Theorem example1: forall P Q:Prop,
     ~(P \/ Q) -> ~P /\ ~Q.
Proof.
    unfold not.
    intros.
    split.
    intro H1.
    apply H.
    left.
    apply H1.
    intro H2.
    apply H.
    right.
    apply H2.
Qed.