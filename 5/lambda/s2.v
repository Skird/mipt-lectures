Check nat -> nat.

Check bool.

Check Set.

Check Type.

Inductive mbool : Type := tr : mbool | fl : mbool.

Definition mneg (x : mbool) : mbool :=
  match x with
    | tr => fl
    | fl => tr
  end.

Definition mand (x y : mbool) :=
  match x with
    | tr => y
    | fl => fl
  end.

Definition mor (x y : mbool) :=
  match x with
    | tr => tr
    | fl => y
  end.

Example test_mor : (mor tr fl = tr) /\ (mor fl tr = tr) /\ (mor fl fl = fl).
Proof.
simpl.
split; [reflexivity | split; reflexivity].
Qed.

Lemma demorgan : forall (x y : mbool), mneg (mand x y) = mor (mneg x) (mneg y).
Proof.
intros.
Print mbool_ind.
apply (mbool_ind (fun (u : mbool) => forall y : mbool, mneg (mand u y) = mor (mneg u) (mneg y))).
apply ( mbool_ind ( fun (v: mbool) => mneg (mand tr v) = mor (mneg tr) (mneg v) ) ).
simpl; reflexivity.
simpl; reflexivity.
simpl.
intro.
reflexivity.
Qed.

Lemma demorgan' : forall (x y : mbool), mneg (mand x y) = mor (mneg x) (mneg y).
Proof.
intros.
destruct x.
  { destruct y.
    - simpl; reflexivity. 
    - simpl; reflexivity.
  }
  { destruct y; simpl; reflexivity. 
  }
Qed.



Lemma ll : forall (x y : mbool), mand x y = mor x y -> x = y.
Proof.
intros.
destruct x.
  { assert (A1 : mand tr y = y).
      { destruct y; simpl; reflexivity. }
    assert (A2 : mor tr y = tr).
      { destruct y; simpl; reflexivity. }
    rewrite <- A1.
    transitivity (mor tr y).
      - symmetry; assumption.
      - symmetry; assumption.
  }
  { assert (A1 : mand fl y = fl).
      { destruct y; simpl; reflexivity. }
    assert (A2 : mor fl y = y).
      { destruct y; simpl; reflexivity. }
    rewrite <- A1.
    transitivity (mor fl y); assumption.
  }
Qed.

Eval compute in mand tr fl.

Inductive color : Type := red | green | blue.

Check red.

Definition f := fun (c : color) =>
  match c with
    | red => green
    | green => blue
    | blue => red
  end.

Compute f(f(f green)).

Lemma ffp : forall (c : color), f( f (f c)) = c.
Proof.
intro.
Search color.
apply (color_ind (fun (x : color) => f( f (f x)) = x)).
simpl; reflexivity.
simpl; reflexivity.
simpl; reflexivity.
Qed.

Lemma ffp' : forall (c : color), f( f (f c)) = c.
Proof.
intros.
destruct c; simpl; reflexivity.
Qed.

Inductive mtree : Type :=
  | nl : mtree
  | node : mtree -> nat -> mtree -> mtree.

Check node.

Definition myTree := node (node nl 3 (node nl 2 nl)) 7
   (node (node nl 1 nl) 3 (node (node nl 4 nl) 5 nl)).

Fixpoint leafNum (t : mtree) : nat := 
  match t with
    | nl => 0
    | node nl _ nl => 1
    | node l _ r => (leafNum l) + (leafNum r)
  end.

Compute leafNum (node nl 2 (node nl 3 nl)).
Compute leafNum myTree.

Search mtree.

Module MyNat.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Search nat.

Fixpoint prd (n : nat) :nat :=
  match n with
    | O => O
    | S p => p
  end.

Compute prd (S(S O)).

Fixpoint add (m n : nat) :=
  match n with
    | O => m
    | S p => S (add m p)
  end.

Fixpoint mlt (m n : nat) :=
  match n with
    | O => O
    | S p => add (mlt m p) m
  end.

Compute mlt (S(S O)) (S(S(S O))).

Example exm1 : S(S O) = add (S O) (S O).
Proof.
simpl.
reflexivity.
Qed.

Fixpoint eq (m n :nat) : bool :=
  match (m,n) with
    | (O,O) => true
    | (S p, O) => false
    | (O, S q) => false
    | (S p, S q) => eq p q
  end.


Lemma l1 : forall n : nat, eq (S n) O = false.
Proof.
intros.
simpl.
reflexivity.
Qed.

Fixpoint le (m n : nat) : bool :=
  match m with
    | O => true
    | S p => match n with
              | O => false
              | S q => le p q
             end
  end.

Example exm2 : le (S O) (S (S O)) = true.
Proof.
simpl. reflexivity.
Qed.

Example exm3 : le (S (S O)) (S O) = false.
Proof.
simpl. reflexivity.
Qed.

Notation "x + y" := (add x y)
                       (at level 50, left associativity).
Notation "x * y" := (mlt x y)
                       (at level 40, left associativity).


Compute (S O) + (S O).

Lemma l2 : forall n : nat, n + O = n.
Proof.
intros.
simpl.
reflexivity.
Qed.

Lemma l2' : forall n : nat, n * O = n.
Admitted.

Lemma l3 : forall n m k: nat, n = m -> m + k = n + k.
Proof.
intros.
rewrite <- H.
reflexivity.
Qed.

Lemma l4 : forall n : nat, n = O \/ exists m : nat, n = S m.
Proof.
intros.
destruct n as [ | p].
{ left. reflexivity. }
{ right.
  exists p.
  reflexivity.
}
Qed.

(* Induction needed... *)
Lemma lerfl : forall n : nat, le n n = true.
Admitted.

(* Induction *)

Lemma l5' : forall n : nat, O + n = n.
Proof.
Check nat_ind.
apply (nat_ind (fun n : nat => O + n = n)).
  - reflexivity.
  - { intros.
      simpl.
      rewrite -> H.
      reflexivity.
    }
Qed.

Lemma l5 : forall n : nat, O + n = n.
Proof.
induction n.
(*induction n as [ | n' IH ].*)
{ reflexivity. }
{ simpl. rewrite -> IHn. reflexivity. }
Qed.

Lemma l6 : forall (n m : nat), S n + m = S (n + m).
Proof.
induction m.
{ simpl. reflexivity. }
(*simpl (n + S m) at 1.*)
{ simpl. rewrite -> IHm. reflexivity. }
Qed.

Lemma l7 : forall (n m : nat), n + m = m + n.
induction n.
{ simpl. intro. exact (l5 m). }
{ intro.
  transitivity (S (n + m)).
  exact (l6 n m).
  simpl.
  assert (H : n + m = m + n). { exact (IHn m). }
  rewrite -> H.
  reflexivity.
}
Qed.

Lemma l8 : forall (n m k : nat), (n + m) + k = n + (m + k).
Proof.
induction k.
{ reflexivity. }
{ simpl. rewrite <- IHk. reflexivity. }
Qed.

Lemma l9' : forall n : nat, eq n n = true.
Proof.
induction n.
- simpl. reflexivity.
- simpl. assumption.
Qed.

Lemma l9 : forall n m : nat, m = n  ->  eq m n = true.
Proof.
intros.
rewrite -> H.
exact (l9' n).
Qed.

Lemma l9a : forall n m : nat, eq m n = eq n m.
Proof.
induction n.
  - destruct m.
      + reflexivity.
      + simpl. reflexivity.
  - intro.
    destruct m.
      + reflexivity.
      + simpl. apply IHn.
Qed.


Lemma l10' : forall m : nat, S m <> O.
Proof.
intro.
intro.
Check eq_ind.
Check eq_ind (S m )(fun x : nat => if x then False else True ) I O.
apply (eq_ind (S m )(fun x : nat => if x then False else True ) I O).
assumption.
Qed.

Lemma l10'' : false <> true.
Proof.
intro.
apply (eq_ind false (fun x : bool => if x then False else True ) I true).
assumption.
Qed.

Lemma l10''' : false <> true.
Proof.
intro.
discriminate H.
Qed.

Lemma l10'''' : forall n : nat, S n <> O.
Proof.
intro.
intro.
discriminate H.
Qed.

Print l10''''.

Lemma l10a : forall m : nat, ~(eq (S m) O = true).
Proof.
intro. intro.
assert (H1 : eq (S m) O = false). { simpl. reflexivity. }
assert (H2 : false = true).
       { transitivity (eq (S m) O); [rewrite <- H1 | rewrite <- H]; reflexivity. }
assert (H3 : false <> true). { exact l10''. }
elim H3; assumption.
Qed.

Lemma l10b  : forall m : nat, ~(eq (S m) O = true).
Proof.
intro. intro.
assert (H1 : eq (S m) O = false). { simpl. reflexivity. }
assert (H2 : false = true).
       { transitivity (eq (S m) O); [rewrite <- H1 | rewrite <- H]; reflexivity. }
discriminate H2.
Qed.

Lemma l10 : forall n m : nat, eq m n = true -> m = n.
Proof.
induction n.
{ intro. destruct m.
  - intro. reflexivity.
  - intro. elim (l10a m). assumption.
}
{ intro. destruct m.
  -  intro.
     elim (l10a n).
     transitivity (eq O (S n)).
      + exact (l9a (S n) O).
      + assumption.
  - simpl. intro.
    cut (m = n). { intro. rewrite <-H0. reflexivity. }
    apply (IHn m). assumption.
}
Qed.

Lemma l11 : forall n : nat, le n n = true.
Proof.
induction n.
- simpl. reflexivity.
- simpl. assumption.
Qed.

End MyNat.









