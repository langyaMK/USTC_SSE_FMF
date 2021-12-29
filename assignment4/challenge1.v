Variables A B: Set.
Variables P: A -> B -> Prop.
Theorem challenge1:
    (exists x, exists y, P x y) -> (exists y, exists x, P x y).
Proof.
    intros.
    destruct H as [a p1].
    destruct p1 as [b p2].
    exists b, a.
    apply p2.
Qed.