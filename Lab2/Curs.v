Inductive Nat :=
| O : Nat
| S : Nat -> Nat.

Check Nat_ind.

Check (S (S O)).
Check S.

Fixpoint plus (k m : Nat) : Nat :=
  match k with
  | O   => m
  | S n => S (plus n m)
  end.

Compute plus O (S (S O)).
Compute plus (S (S O)) (S (S O)).

Lemma plus_O_n_is_n :
  forall n , plus O n = n.
Proof.
  intro n.
  simpl.
  reflexivity.
Qed.

Theorem plus_eq:
  forall m n,m = n -> plus O m = plus O n.
Proof.
  intros m n.
  simpl.
  intro H.
  rewrite H.
  reflexivity.
Qed.
  
Theorem plus_mn_eq_plus_nn :
  forall m n , m = n -> plus m n = plus n n.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Theorem plus_mn_eq_plus_mm :
  forall m n, m = n -> plus m n = plus m m.
Proof.
  intros.
  rewrite H.
  trivial.
Qed.

Theorem plus_c_a :
  forall k , plus k (S O) <> O .
Proof.
    intros.
    destruct k as [ |k']eqn:E.
    -simpl. unfold not. intro H. inversion H.
    -simpl. unfold not. intro H. inversion H.
Qed.

Theorem plus_c_a' :
    forall k , plus k (S O) <> O .
Proof.
  intros.
  unfold not.
  intro H.
  destruct k as [|k']eqn:E.
  -simpl in H. inversion H.
  -simpl in H. inversion H.
Qed.

Check Nat_ind.

Theorem plus_n_O_is_n : 
  forall n , plus n O = n.
Proof.
  induction n.
  -simpl. reflexivity.
  -simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_n_Sn_is_S_n_m : 
  forall n m, plus n (S m) = S(plus n m).
Proof.
  intro n.
  induction n.
  -intro m. simpl. reflexivity. 
  -intro m. simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_exercise_1:
  forall n, plus n (plus n O) = plus n n.
Proof.
  induction n.
  - simpl. trivial.
  - simpl. 
      rewrite plus_n_Sn_is_S_n_m.
      rewrite plus_n_Sn_is_S_n_m.
      rewrite IHn.
      reflexivity.
Qed.

(*
Theorem nat_plus_c_a :
    forall k, plus k (S O) <> (S O) .
Proof.
  intro k.
  destruct k as [|k']eqn:E.
  -simpl. unfold not. intro H. 
*)
(*
Theorem nat_plus_n_0_is_n : 
    forall n , plus n O = n.
Proof.
  *)
Lemma plus_m_O_is_m:
  forall m,
    plus m O = m.
Proof.
  induction m.
  - simpl. reflexivity.
  - simpl. rewrite IHm. reflexivity.
Qed.
Lemma plus_n_Sm_is_Snm:
  forall n m,
    plus n (S m) = S (plus n m).
Proof.
  induction n.
  - intro m. simpl. reflexivity.
  - intro m. simpl. rewrite IHn. reflexivity.
Qed.
Lemma plus_comm:
  forall m n,
    plus m n = plus n m.
Proof.
     induction m;intro n;simpl.
  -rewrite plus_m_O_is_m;reflexivity.
  -rewrite plus_n_Sm_is_Snm; rewrite IHm.
   reflexivity.
Qed.

