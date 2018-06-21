Fixpoint sum_n n : nat :=
  match n with
  | 0 => 0
  | S p => sum_n p + S p
  end.

Compute sum_n 3.

Require Import ArithRing.

Lemma l1 : forall n, 2 * sum_n n = n * n + n.
Proof.
induction n.
  - simpl. reflexivity.
  - assert (H : S n * S n = n * n +  n + n + 1 ).
     { ring. }
    rewrite -> H.
    rewrite <- IHn.
    simpl (sum_n (S n)).
    ring.
Qed.

Fixpoint sqsum_n n : nat :=
  match n with
  | 0 => 0
  | S p => sqsum_n p + (S p)*(S p)
  end.

Compute sqsum_n 3.


Lemma l2 : forall n, 6 * sqsum_n n = n * (n + 1) * (2 * n + 1).
Proof.
induction n.
  - reflexivity.
  - simpl (sqsum_n (S n)).
    ring_simplify.
    rewrite -> IHn.
    ring.
Qed.

Fixpoint fac n : nat :=
  match n with
  | 0 => 1
  | S p => (S p) * (fac p)
  end.

Compute fac  6.

Fixpoint binom (n k : nat) :=
  match (n,k) with
  | (_, 0)   =>  1
  | (0, S q) =>  0
  | (S p, S q) => binom p (S q) + binom p q
  end.

Compute binom 7 11.
Compute binom 4 2.

Lemma l3a : forall n, binom n 0 = 1.
Proof.
destruct n. reflexivity.
simpl. ring.
Qed.

Lemma l3b : forall n, binom n 1 = n.
Proof.
induction n.
reflexivity.
simpl. rewrite IHn.
rewrite (l3a n).
ring.
Qed.

Require Import Omega.

Lemma l3c : forall n k : nat, k <= n ->  (n - k) * binom n k = (k + 1) * binom n (S k).
Admitted.

Require Import Bool.

Fixpoint evenb (n : nat) :=
  match n with
  | 0 => true
  | S p => negb (evenb p)
  end.

Compute evenb 1.

Lemma l4 : forall n, evenb n = true -> exists x, n = 2 * x.
Proof.
assert (S: forall n, (evenb n = true -> exists x, n = 2 * x) /\
(evenb (S n) = true -> exists x, S n = 2 * x)).
- induction n.
  split.
  + intro.
    exists 0. reflexivity.
  + intro.
    simpl (evenb 1) in H.
    discriminate H.
  + split.
    destruct IHn.
    assumption.
    simpl. intros. destruct IHn.
    assert (H2 : forall b, b = negb (negb b)). { destruct b; reflexivity. }
    assert (H3 : evenb n = true ). { transitivity (negb ( negb (evenb n))).
                                     exact (H2 (evenb n)).
                                     exact H. }
    assert (H4 : exists x : nat, n = 2 * x ). { exact (H0 H3). }
    elim H4.
    intros.
    exists (x + 1).
    rewrite H5.
    ring.
- apply S.
Qed.

Require Import List.

Fixpoint rev (l : list nat) :=
  match l with 
  | nil => nil
  | x :: xs => rev xs ++ (x :: nil)
  end.

Fixpoint length (l : list nat) :=
  match l with
  | nil => 0
  | x :: xs => length xs + 1
  end.

Lemma lA : forall l m, length (l ++ m) = length l + length m.
Proof.
intros.
induction l.
- reflexivity.
- simpl. rewrite -> IHl. ring.
Qed.

Lemma lB : forall l, length (rev l) = length l.
Proof.
induction l.
- reflexivity.
- simpl. rewrite -> lA.
  rewrite -> IHl. reflexivity.
Qed.


Fixpoint count (n : nat) (l : list nat) :=
match l with
  | nil => 0
  | x :: xs =>
    let r := count n xs in if beq_nat n x then 1 + r else r
  end.

Compute count 5 (2::5::1::5::nil).


Fixpoint ins n l :=
  match l with
    |nil => n::nil
    |x :: xs => if n <=? x then n::l else x :: ins n xs
  end.

Lemma l5 : forall n l, count n (ins n l) = S (count n l).
Proof.
intros.
induction l.
- simpl.
  Search beq_nat.
  Check beq_nat_refl.
  rewrite <- beq_nat_refl.
  reflexivity.
- simpl.
  case (n <=? a).
(*  destruct (n <=? a). *)
  simpl.
  rewrite <- beq_nat_refl. reflexivity.
  simpl.
  rewrite IHl.
  case (n =? a); ring.
Qed.

Lemma l5a : forall n m l, n =? m = false -> count n (ins m l) = count n l.
Proof.
intros.
induction l.
- simpl. rewrite H. reflexivity.
- simpl. case (m <=? a).
  case (n ?= a).
  simpl. rewrite H. reflexivity.
  simpl. rewrite H. reflexivity.
  simpl. rewrite H. reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.
  
Definition insort := fix f (l : list nat) : list nat :=
                        match l with
                          |nil => nil
                          |x :: xs => ins x (f xs)
                        end.

Check insort.

Lemma l6 : forall n l, count n (insort l) = count n l .
Proof.
intros.
induction l.
- reflexivity.
- simpl.
  assert (n =? a = true \/ n =? a = false). { case (n =? a); [left | right]; reflexivity. }
  elim H.
  + intro.
    rewrite H0.
    rewrite <- IHl.
    Check beq_nat_true.
    assert (H1 : n = a). { apply (beq_nat_true n a). assumption. }
    rewrite <- H1.
    exact (l5 n (insort l)).
  + intro.
    rewrite H0.
    rewrite <- IHl.
    apply (l5a n a (insort l)).
    assumption.
Qed.

Fixpoint sorted (l : list nat) : bool :=
  match l with
    |nil => true
    |x :: xs => match xs with
                  |nil => true
                  |y :: ys => andb (x <=? y) (sorted xs)
                end
  end.

Definition myList := 1::2::2::3::4::nil.

Compute sorted myList.
Compute sorted (rev myList).

Print andb_true_eq.

Lemma l7a : forall n l, sorted (n :: l) = true -> sorted l = true.
Proof.
induction l.
- simpl. auto.
- intro. simpl in H.
  Search andb.
  assert (H1: (n <=? a) = true  /\ (match l with
    nil => true | y :: _ => (a <=? y) && sorted l end) = true).
    { apply (andb_true_iff (n <=? a)
       (match l with nil => true | y :: _ => (a <=? y) && sorted l end)).
      assumption.
    }
  destruct l.
  + reflexivity.
  + elim H1. intros.
    rewrite <- H2.
    simpl. reflexivity.
Qed.

Axiom leb_total : forall (m n : nat), m <=? n = false -> n <=? m = true.

Lemma l7b : forall n m l l', ins n l = m :: l' -> m <=? n = true.
Proof.
intros.
case l in H.
- simpl  in H.
  injection H.
  intros.
  rewrite H1.
  Search Nat.leb.
  apply (Nat.leb_refl).
- simpl in H.
  assert (H1 : n <=? n0 = true \/ n <=? n0 = false).
    {  case (n <=? n0); [left | right]; reflexivity. }
  elim H1.
  + intro.
    rewrite H0 in H.
    injection H. intros. rewrite H3. apply (Nat.leb_refl).
  + intro. 
    rewrite H0 in H.
    injection H. intros.
    rewrite <- H3.
    assert ((n0 <=? n) = true).
      { apply (leb_total n n0). assumption. }
    assumption.
Qed.

Lemma l7c : forall n m m' l l', ins n (m :: l) = m' :: l' -> m' <=? m = true.
Proof.
intros.
case l in H.
-  simpl in H.
   assert (H1 : n <=? m = true \/ n <=? m = false).
    {  case (n <=? m); [left | right]; reflexivity. }
   elim H1.
    + intro. rewrite -> H0 in H.
      injection H. intros.
      rewrite <- H3. assumption.
    + intro.
      assert (H2 : (m <=? n) = true).
      { apply (leb_total n m). assumption. }
      rewrite -> H0 in H.
      injection H. intros.
      rewrite <- H4.
      apply (Nat.leb_refl).
- simpl in H. 
   assert (H1 : n <=? m = true \/ n <=? m = false).
    {  case (n <=? m); [left | right]; reflexivity. }
   elim H1.
    + intro. rewrite -> H0 in H.
      injection H. intros.
      rewrite <- H3. assumption.
    + intro.
      assert (H2 : (m <=? n) = true).
      { apply (leb_total n m). assumption. }
      rewrite -> H0 in H.
      assert (H3 : n <=? n0 = true \/ n <=? n0 = false).
       { case (n <=? n0); [left | right]; reflexivity. }
      elim H3.
        { intro.
          rewrite -> H4 in H. injection H. intros.
          rewrite <- H6.
          apply (Nat.leb_refl).
        }
        { intro.
          rewrite -> H4 in H.  injection H. intros.
          rewrite <- H6.
          apply (Nat.leb_refl).
        }
Qed.

Lemma l7d : forall a b l n y l', a <=? b = true /\
     (a <=? n = true /\ ins n (b :: l) = y :: l') -> a <=? y = true.
Proof.
intros.
elim H. intro. intro. elim H1. intros.
simpl in H3.
assert (H4 : n <=? b = true \/ n <=? b = false).
  { case (n <=? b); [left | right]; reflexivity. }
elim H4.
- intro.
  rewrite H5 in H3.
  injection H3. intros.
  rewrite <- H7. assumption.
- intro.
  rewrite H5 in H3.
  injection H3. intros.
  rewrite <- H7. assumption.
Qed.

Lemma l7 : forall n l, sorted l = true -> sorted (ins n l) = true.
Proof.
induction l.
- simpl. intro. assumption.
- intro. simpl.
  assert (n <=? a = true \/ n <=? a = false). {
   case (n <=? a); [left | right]; reflexivity. }
  elim H0.
  + intro.
    rewrite H1.
    transitivity (true && true).
    rewrite <- H1 at 1.
    rewrite <- H.
    simpl. reflexivity.
    reflexivity.
  + intro.
    rewrite H1.
    simpl.
    assert (H2 : sorted l = true).
      { apply (l7a a l). exact H. }
    assert (H3 : sorted (ins n l) = true).
      { exact (IHl H2). }
    rewrite H3.
    assert (H4 : (a <=? n) = true).
      { apply (leb_total n a). assumption. }
    assert (H5 : forall b l', l = b :: l' -> a <=? b = true).
      { intros.
        rewrite -> H5 in H.
        simpl in H.
        assert (H6: (a <=? b) = true  /\ (match l' with
         nil => true | b0 :: _ => (b <=? b0) && sorted l' end) = true).
         { apply (andb_true_iff (a <=? b)
          (match l' with
             nil => true | b0 :: _ => (b <=? b0) && sorted l' end)).
           assumption.
         }
         elim H6. intros. assumption.
      }
    assert (H7 : forall y l1, ins n l = y :: l1 -> a <=? y = true ).
      { intros.
        destruct l as [ | b l'].
         { simpl in H6. injection H6. intros.
           rewrite <- H8. assumption.
         }
         { assert (H8 : a <=? b = true).
             { apply (H5 b l'). reflexivity. }
           apply (l7d a b l' n y l3).
           auto.
         }
       }
    destruct (ins n l).
      { reflexivity. }
      { assert (H8 : a <=? n0 = true).
          { apply (H7 n0 l0). reflexivity. }
        rewrite -> H8.
        reflexivity.
      }
Qed.

Lemma l8 : forall l, sorted (insort l) = true.
Proof.
induction l.
- simpl. reflexivity.
- simpl. apply l7. assumption.
Qed.

(* Thus the correctnes of insort has been verified. *)

Lemma l9a : forall l a, sorted (a :: l) = true -> ins a l = a :: l.
Proof.
intros.
induction l.
- reflexivity.
- simpl. 
  assert (a <=? a0= true \/ a <=? a0 = false). {
   case (a <=? a0); [left | right]; reflexivity. }
  elim H0.
  + intro.
    rewrite -> H1. reflexivity.
  + intro.
    rewrite -> H1.
    simpl in H.
    assert (H2: (a <=? a0) = true  /\ (match l with
         nil => true | y :: _ => (a0 <=? y) && sorted l end) = true).
      { apply (andb_true_iff (a <=? a0)
         (match l with
            nil => true | y :: _ => (a0 <=? y) && sorted l end)).
          assumption.
       }
    assert (H3 : (a <=? a0) = true).
      { elim H2.
        intros. assumption.
      }
    assert (H4 : true = false).
      { rewrite <- H1.
        rewrite H3. reflexivity.
      }
    discriminate H4.
Qed.


Lemma l9 : forall l, sorted l = true -> insort l = l.
Proof.
induction l.
- simpl. auto.
- intro.
  simpl.
  assert (H1 : sorted l = true).
    { apply (l7a a l). assumption. }
  assert (H2 : insort l = l).
    { exact (IHl H1). }
  rewrite -> H2.
  simpl.
  apply (l9a l a).
  assumption.
Qed.

Fixpoint filter (f:nat -> bool) (l: list nat) : list nat :=
  match l with
    |nil => nil
    |x :: xs => if f x then x :: filter f xs else filter f xs
  end.

Eval compute in 3 <=? 2.

Eval compute in filter (fun x => 2 <=? x) myList.


Fixpoint qsort' (n : nat) (l:list nat)  : list nat :=
match n with
  |0 => nil
  |S p =>  match l with
            |nil => nil
            |x :: xs => let less := filter (fun y => y <=? x) xs in
                        let greater := filter (fun y => x <? y) xs in
                        qsort' p less ++ (x :: nil) ++ qsort' p greater
           end
end.

Definition qsort := fun (l : list nat) => qsort' (length l) l.

Compute qsort (rev myList ++ (8 :: 3 :: 11 :: 2 :: 2 :: 5 :: nil)).

