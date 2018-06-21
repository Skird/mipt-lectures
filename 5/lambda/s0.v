Check (3,1=2).

Check let f := fun (x:nat) (y:nat) => x < y in f 2 3 \/ not(3 = 7).

Definition f := fun (x:nat) y (z:nat) (u:nat) (v:nat) => x + y + z + u + v.

Check f.

Eval compute in f 1 2 3 4 5.

Definition g x := x*x + 3*x.

Check g.

Print g.

Definition h := fun n m : nat =>
    (let d := n - m in
      let sq := d * d in
        sq * (sq + n)).

Check h.


(*Require Import Bool.*)

Require Import Arith.

Definition isZero := fun (n:nat) =>
  match n with
   |0 => true
   |S_ => false
  end.

Check isZero.
Print isZero.


Fixpoint fac (n:nat) :=
  match n with
    |0 => 1
    |S p => n * (fac p)
  end.

Print fac.

Eval compute in fac 6.

Fixpoint fib (n:nat) :=
  match n with
    |0 => 0
    |S p => match p with
              |0 => 1
              |S q => (fib p) + (fib q)
            end
  end.

Eval compute in fib 5.


Fixpoint add (n:nat) (m:nat) :=
  match n with
    |0 => m
    |S p => S (add p m)
  end.

Eval compute in add 19 17.

Fixpoint mlt (m n:nat) {struct n} :=
  match n with
    |O => 0
    |S p => m + (mlt m p)
end.

Eval compute in mlt 7 13.

Fixpoint acker (m:nat) (n:nat) :=
  match m with
    |0 => n + 1
    |S p => let fix ac1 (n:nat) :=
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

Eval compute in map (fun x => x*x) myL.

Eval compute in myL ++ myL.

Fixpoint count (n:nat) : list nat :=
  match n with
    |0 => nil
    |S p => count p ++ (p :: nil)
  end.

Eval compute in count 5.

Fixpoint ins n l :=
  match l with
    |nil => n::nil
    |x :: xs => if n <=? x then n::l else x :: ins n xs
  end.

Check ins.

Definition insort := fix f (l : list nat) : list nat :=
                        match l with
                          |nil => nil
                          |x :: xs => ins x (f xs)
                        end.

Check insort.

Eval compute in insort (myL ++ (count 6) ++ myL).

Fixpoint filter (f:nat -> bool) (l: list nat) : list nat :=
  match l with
    |nil => nil
    |x :: xs => if f x then x :: filter f xs else filter f xs
  end.

Eval compute in 3 <=? 2.

Eval compute in filter (fun x => 2 <=? x) myL.



(*Fixpoint qsort (l:list nat) : list nat :=
  match l with
    |nil => nil
    |x :: xs => let less := filter (fun y => y <=? x) xs in
                    let greater := filter (fun y => x <? y) xs in
                      qsort less ++ (x :: nil) ++ qsort greater
  end.
*)



