Variables A B C: Prop.
Lemma L1: A -> A.
  intro.
  assumption.
Qed.
Print L1.
Check L1.
Lemma L2: (A -> B) -> (B ->C) -> (A -> C).
  intros.
  apply H0.
  apply H.
  exact H1.
Qed.
Print L2.
Lemma L3: ((((A -> B) -> A) -> A) -> B) -> B.
  intro.
  apply H.
  intro.
  apply H0.
  intro.
  apply H.
  intro.
  exact H1.
Qed.
Print L3.

Check (3,1=2).
Definition f := fun (x: nat) (y: nat) => x + y.
Definition f1 := fun (x y: nat) => x + y.
Definition f2 := fun x y => x + y.
Definition g (x: nat)(y: nat) := x * y.
Eval compute in f 3 5.

Definition isZero (n: nat) :=
  match n with
    | 0 => true
    | S _ => false
  end.
Check isZero.
Check True.
Check true.
Print isZero.