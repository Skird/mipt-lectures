Section Sct0.

Hypotheses P Q R T: Prop.

Lemma ex1 : P -> Q -> (P -> Q -> R) -> R.
Proof.
intros.
apply H1; assumption.
Qed.

Lemma ex2 : (((P -> Q) -> Q) -> Q) -> P -> Q.
Proof.
intros; apply H; intro H1; apply H1; assumption.
Qed.

Lemma ex3 : (P -> Q -> R) -> (P -> Q) -> (P -> R).
Proof.
intros H1 H2 H3.
apply H1; [assumption | apply H2; assumption].
(*apply H1; assumption || (apply H2; assumption).*)
Qed.

Lemma ex4 : (P -> Q) -> (P -> R) -> (P -> Q -> R -> T) -> P -> T.
Proof.
intros.
apply H1; [idtac | apply H | apply H0]; assumption.
Qed.


End Sct0.

(*Check P.*)



(**********************)


Lemma l1 : forall a b : Prop, a /\ b -> b /\ a.
Proof.
intros.
split.
elim H.
intros.
assumption.
elim H.
intros.
assumption.
Qed.

Print l1.

Check and_ind.
Check conj.

Lemma l2 : forall a b : Prop, a \/ b -> b \/ a.
Proof.
intros.
elim H.
intro.
right.
exact H0.
intro.
left.
assumption.
Qed.

Print l2.

Check or_ind.
Check or_introl.

Lemma l3 : forall a b c : Prop, a /\ (b /\ c) -> (a /\ b) /\ c.
Proof.
intros.
split.
split.
elim H.
intros.
assumption.
elim H; intros; elim H1; intros; assumption.
elim H; intros; elim H1; intros; assumption.
Qed.

Print l3.

Lemma l4 : forall a b c : Prop, a <-> a /\ (a \/ b).
split.
intro.
split.
exact H.
left; assumption.
(*apply (or_introl H).*)
intro.
elim H.
intros; assumption.
Qed.

Print l4.

Lemma l4' : forall a b c : Prop, a <-> b -> (a \/ c) <-> (b \/ c).
Proof.
split.
elim H.
intros.
elim H2.
intro.
left.
apply H0.
assumption.
intro; right; assumption.
intro; elim H0.
elim H.
intros.
left; apply H2; assumption.
intro; right; assumption.
Qed.

Print l4'.



Lemma l5 : forall a b c : Prop, a \/ (b /\ c) -> (a \/ b) /\ (a \/ c).
split.
elim H.
left; assumption.
intro.
elim H0.
intros.
right.
assumption.
elim H; [ left; assumption | intro; elim H0; intros; right; assumption].
Qed.

Print l5.

Search False.
Print neg_false.

Lemma l6 : forall a : Prop, ~(a /\ ~a).
Proof.
intro.
intro.
elim H.
intros.
elim H1.
assumption.
Qed.

Print l6.
Print False_rect.

Lemma l7 : forall a : Prop, a -> ~~a.
Proof.
intros.
intro.
elim H0.
assumption.
Qed.

Variable R : Prop.
Check l7 R.

Lemma l8 : forall a : Prop, ~~~a -> ~a.
Proof.
intros.
intro.
elim H.
apply (l7 a).
assumption.
Qed.

Section Classic.

Axiom tnd : forall a : Prop, ~a \/ a.

Search or.
Print or_ind.

Lemma d_neg0 : forall a : Prop, (~a \/ a) -> ~~a -> a.
Proof.
intros.
elim H.
2:intro; assumption.
intro.
elim H0.
assumption.
Qed.

Lemma d_neg : forall a : Prop, ~~a -> a.
Proof.
intro.
apply (d_neg0 a).
exact (tnd a).
Qed.

Print d_neg.

Lemma d_neg' : forall a : Prop, ~~a -> a.
Proof.
intro.
cut (~a \/ a).
exact (d_neg0 a).
exact (tnd a).
Qed.

End Classic.

Print d_neg.
Print d_neg'.


Section Sct1.
Check ex_intro.

Variable T : Type.
Variable x : T.

Lemma l9 : forall (P : T -> Prop), (forall n : T, P n) -> (exists n : T, P n).
Proof.
intros.

exists x.
(*apply (ex_intro P x).*)
apply H.
Qed.

Print l9.

Lemma l10 : forall (P : T -> T -> Prop), (exists m : T, forall n : T, P n m) -> (forall n : T, exists m : T, P n m).
Proof.
intro.
intro.
elim H.
intro.
intro.
intro.
exists x0.
apply H0.
Qed.

Print l10.

Lemma l11 : forall (P Q : T -> Prop), (forall n : T, P n -> Q n) -> (exists n : T, P n) -> (exists n : T, Q n).
Proof.
intros.
elim H0.
intros.
exists x0.
apply (H x0).
(*apply H.*)
assumption.
Qed.

Print l11.

Lemma l12 : forall (P Q : T -> Prop), (exists n : T, P n -> Q n) -> (forall n : T, P n) -> (exists n : T, Q n).
Proof.
intros.
elim H.
intros.
exists x0.
apply H1.
exact (H0 x0).
(* apply H0. *)
Qed.

Lemma l13_cl : forall (P : T -> Prop) (Q : Prop), (forall n : T, P n \/ Q) -> (forall n : T, P n) \/ Q.
Proof.
intros.
cut (~Q \/ Q).
intro.
elim H0.
intro.
left.
intro.
elim (H n).
intro; assumption.
intro.
elim H1.
assumption.
intro; right; assumption.
exact (tnd Q).
Qed.

Print l13_cl.

Lemma l14 : forall (P : T -> T -> T -> Prop), (forall t : T, exists n : T, forall m : T, P t n m )-> (forall z : T, exists w : T, P z w z).
Proof.
intros.
cut (exists n : T, forall m : T, P z n m).
intro.
elim H0.
intros.
exists x0.
exact (H1 z).
exact (H z).
Qed.

Print l14.

End Sct1.















