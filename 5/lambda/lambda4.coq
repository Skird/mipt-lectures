Variables A B C: Prop.

Lemma l1: A -> B -> A.
Proof.
intros X Y.
exact X.
Qed.

Check l1.
Print l1.

Fixpoint fac (n: nat) :=
  match n with
    |0 => 1
    |S p => n * (fac p)
  end.

Print fac.

Fixpoint fib (n: nat) :=
  match n with
    |0 => 1
    |S p => match p with
              |0 => 1
              |S q => (fib p) + (fib q)
            end
  end.

Eval compute in fib 6.

Fixpoint acker (m: nat) (n: nat) :=
  match m with
    |0 => n + 1
    |S p => let fix ac1 (n: nat) :=
              match n with
                |0 => acker p 1
                |S q => acker p (ac1 q)
              end
            in ac1 n
  end.

Eval compute in acker 4 0.

Require Import List.

Definition myL := 1::2::3::nil.

Check myL.

Eval compute in myL ++ myL.

Eval compute in map (fun x => x * x) myL.

Fixpoint count(n: nat) : list nat :=  
  match n with
    |0 => nil
    |S p => count p++ (p:: nil)
  end.

Eval compute in count 5.

(*
 Fixpoint ins n l :=
  match l with
    |nil => n::nil
    |x :: xs => if leq n x then n::l else x :: ins n xs
  end.
*)

Fixpoint filter (f: nat -> bool) (l: list nat): list nat := 
  match l with
    |nil => nil
    |x :: xs => if f x then x :: filter f xs else filter f xs
  end.

(*
Fixpoint qsort(l: list nat): list nat :=
  match l with
    |nil => nil
    |x :: xs => let less: filter (fun y => y <=? x) xs in
                  let greater := filter (fun y => x <? y) xs in
                    qsort less ++ (x :: nil) ++ qsort greater
  end.
*)