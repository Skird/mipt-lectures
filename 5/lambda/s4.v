Inductive even : nat -> Prop :=
  | even0 : even 0
  | evenS : forall x:nat, even x -> even (S (S x)).

Check even0.

Example ex0 : even 4.
Proof.
apply (evenS 2).
apply evenS.
exact even0.
Qed.

Example ex1 : ~(even 3).
Proof.
intro.
inversion H.
inversion H1.
Qed.

Require Import ArithRing.

Lemma l0 : forall x, even x -> exists y, x = 2 * y.
Proof.
intros.
induction H.
  - exists 0. reflexivity.
  - elim IHeven.
    intros.
    exists (S x0).
    rewrite -> H0.
    ring.
Qed.

Lemma l1 : forall x, even (S (S x)) -> even x.
Proof.
intros.
inversion H.
assumption.
Qed.

Inductive tree : Set :=
  | nil : tree
  | node : tree -> nat -> tree -> tree.


Inductive In (x:nat) : tree -> Prop :=
  | In_left : forall l r y, In x l -> In x (node l y r)
  | In_right : forall l r y, In x r -> In x (node l y r)
  | Is_root : forall l r, In x (node l x r).

Definition myTree := node (node nil 3 (node nil 2 nil)) 7
   (node (node nil 1 nil) 3 (node (node nil 4 nil) 5 nil)).

(* Of course, there're no 'reduction' of
  a true proposition to True... *)
Compute (In 5 myTree).

Example ex2 : In 5 myTree.
Proof.
apply In_right.
apply In_right.
apply Is_root.
Qed.


(* The proof looks like a search for 0 in myTree...*)
Example ex3 : ~(In 0 myTree).
Proof.
intro.
inversion H.
  { inversion H1.
    { inversion H5. }
    { inversion H5.
      { inversion H7. inversion H9. }
      { inversion H9. }
    }
  }
  { inversion H1.
    { inversion H5.
      { inversion H9. }
      { inversion H9. }
    }
    { inversion H5.
      { inversion H9.
         { inversion H13. }
         { inversion H13. }
      }
      { inversion H8.
        inversion H9.
      }
    }
  }
Qed.


Definition is_empty (t : tree) : bool :=
 match t with
  | nil => true
  | _ => false
 end.

Compute (is_empty myTree).
Compute (is_empty nil).

Lemma l3 : forall t, (is_empty t) = true <->
   forall x, ~(In x t).
Proof.
intros.
case t.
 - simpl. split.
   + intros.
     intro. inversion H0.
   + intro. reflexivity.
 - intros. split.
   + intros. intro.
     simpl in H. discriminate H.
   + intro. simpl.
     Search False.
     apply False_ind.
     assert (H1 : ~ In n (node t0 n t1)).
      { apply H. }
     elim H1.
     apply Is_root.
Qed.

(* Search in BST (w.r.t. arbitrary order). *)

Inductive order : Set := Lt | Eq | Gt.
Hypothesis compare : nat -> nat -> order.

Fixpoint member (x:nat) (t:tree) {struct t} : bool :=
  match t with
  | nil => false
  | node l y r =>
     match compare x y with
      | Lt => member x l
      | Eq => true
      | Gt => member x r
     end
end.

Extraction Language Haskell.
Extraction In.
Extraction member.
Extraction order.
Extraction compare.

Inductive bst : tree -> Prop :=
  | bst_nil : bst nil
  | bst_node : forall x l r, bst l -> bst r ->
      (forall y, In y l -> y < x) ->
        (forall y, In y r -> x < y) -> bst (node l x r).

Definition tr1 := node (node nil 2 nil) 3 
  (node (node nil 4 nil) 6 (node nil 7 nil)).

(*Require Import Decidable PeanoNat.
Check Nat.eq_dec.*)

Lemma frenzy : forall n, forall x, In x (node nil n nil) -> x = n.
Proof.
intro. induction x.
  - induction n.
     + reflexivity.
     + intro. inversion H.
       inversion H1.
       inversion H1.
  - intro.
    inversion H.
    inversion H1.
    inversion H1.
    reflexivity.
Qed.

(* For inequalities. *)
Require Import Omega.

Example ex4 : bst tr1.
Proof.
apply bst_node.
 - apply bst_node; exact bst_nil || (intros; inversion H).
 - apply bst_node; (apply bst_node; exact bst_nil || (intros; inversion H)) || idtac.
   + intros.
     assert (H1 : y = 4).
       { apply frenzy. assumption. }
     rewrite -> H1.
     omega.
   + intros.
     assert (H1 : y = 7).
       { apply frenzy. assumption. }
     rewrite -> H1.
     omega.
 - intros.
     assert (H1 : y = 2).
       { apply frenzy. assumption. }
     rewrite -> H1.
     omega.
 - intros.
   inversion H.
    + assert (H4 : y = 4).
        { apply frenzy. assumption. }
      rewrite -> H4; omega.
    + assert (H4 : y = 7).
        { apply frenzy. assumption. }
      rewrite -> H4; omega.
    + omega.
Qed.

Hypothesis compare_spec : forall x y,
  match compare x y with
    | Lt => x < y
    | Eq => x = y
    | Gt => x > y
  end.

Theorem member_correctness : forall x t, bst t ->
   ((member x t) = true <-> In x t).
Proof.
intro. induction t.
 - intro. simpl.
   split.
    + intro; discriminate.
    + intro. inversion H0.
 - intro. simpl.
(*   cut (compare_spec x n).*)
   generalize (compare_spec x n).
   destruct (compare x n).
    + intro. split.
        { intro. inversion H.
          assert (In x t1).
            { apply IHt1; assumption. }
          apply In_left. assumption. 
        }
        { intro.
          assert (In x t1).
            { inversion H.
              inversion H1.
               { assumption. }
               { assert (n < x).
                  { exact (H8 x H10). }
                 Search lt.
                 Check Nat.lt_asymm.
                 assert (~ x < n). 
                  { apply Nat.lt_asymm.
                   assumption.
                  }
                 elim H14. assumption.
               }
               { assert (~ n < n).
                  { apply Nat.lt_irrefl. }
                 rewrite <- H11 in H9 at 1.
                 elim H9. assumption.
               }
            }
          inversion H.
          apply IHt1; assumption.
         }
    + intro.
      split.
        { intro. rewrite H0.
          apply Is_root.
        }
      reflexivity.
    + (* Symmetrical to the 1st +. *)
      intro. split.
        { intro. inversion H.
          assert (In x t2).
            { apply IHt2; assumption. }
          apply In_right. assumption. 
        }
        { intro.
          assert (In x t2).
            { inversion H.
              inversion H1.
               { assert (x < n).
                  { exact (H7 x H10). }
                 assert (~ x < n). 
                  { apply Nat.lt_asymm.
                    exact H0.
                  }
                 elim H14. assumption.
               }
               { assumption. }
               { assert (~ n < n).
                  { apply Nat.lt_irrefl. }
                 rewrite <- H11 in H9 at 2.
                 elim H9. assumption.
               }
            }
          inversion H.
          apply IHt2; assumption.
         }
Qed.

(* partial maps *)

Definition root' (t : tree) : option nat :=
  match t with
   | nil => None
   | (node l x r) => Some x
  end.

Compute root' nil.
Compute root' myTree.

Definition root : forall t : tree, ~t = nil -> nat.
Proof.
induction t.
  - intro. elim H. reflexivity.
  - intro. exact n.
Defined.

Print root.
Extraction root.
Extraction Language Ocaml.
Extraction root.

Theorem root_correctness : forall t,
  forall h : ~t = nil, forall l x r,
     t = node l x r  -> (root t h) = x.
Proof.
intros.
destruct t.
  - elim h. reflexivity.
  - simpl. injection H.
    intros. assumption.
Qed.

Definition min : forall t : tree, ~t = nil -> nat.
Proof.
induction t.
  - intro. elim H. reflexivity.
  - destruct t1.
     + intro. exact n.
     + intro. apply IHt1.
       intro. discriminate.
Defined.

Print min.
Extraction Language Haskell.
Extraction min.
Extraction Language Ocaml.
Extraction min.

Theorem min_correctness : forall t,
  forall h : ~t = nil, bst t -> 
    In (min t h)  t /\ forall x,
       In x t -> (min t h) <= x.
Proof.
intros.
split.
  - induction t.
     + elim h. reflexivity.
     + destruct t1.
        { simpl.
          apply Is_root.
        }
        { apply In_left.
          apply IHt1.
          inversion H.
          assumption.
        }
  - intros.
    induction t.
      + elim h. reflexivity.
      + Admitted.

Definition min' : forall t,
   ~t = nil -> bst t ->
    { n:nat | In n t /\ forall x, In x t -> n <= x }.
Proof.
Admitted.



