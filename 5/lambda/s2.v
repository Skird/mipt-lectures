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

Inductive mtree : Type :=
  | nil : mtree
  | node : mtree -> mtree -> mtree.

Check node.

Definition myTree := node (node nil (node nil nil)) (node (node nil nil) (node (node nil nil) nil)).

Fixpoint leafNum (t : mtree) : nat := 
  match t with
    | nil => 0
    | node nil nil => 1
    | node l r => (leafNum l) + (leafNum r)
  end.

Compute leafNum (node nil (node nil nil)).
Compute leafNum myTree.

Search mtree.



