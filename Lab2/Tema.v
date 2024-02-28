
(*---------ex1----------*)
Inductive Nat := 
| O : Nat 
| S : Nat -> Nat.

Definition one := S O.
Definition two := S one.
Definition three := S two.
Definition four := S three.
Definition five := S four.

Fixpoint le_Nat (m n : Nat) : bool :=
  match m ,n with
  | O , _         => true 
  | _ , O         => false  
  | (S m'),(S n') => le_Nat m' n'
end.

Compute le_Nat five  (S(S five)). (*true*)
Compute le_Nat O O. (*true*)
Compute le_Nat O one. (*true*)
Compute le_Nat one O. (*false*)
Compute le_Nat one one.
Compute le_Nat one five.
Compute le_Nat five one. (* false *)
Compute le_Nat five four. (* false *)
Compute le_Nat five five. (* true *)

Fixpoint max (m n : Nat) : Nat :=
  match m with
  | O => n
  | S m' => match n with
            | O => m
            | S n' => S (max m' n')
            end
  end.

Compute max one two.
Compute max O one.
Compute max one O.
Compute max four five.
Compute max five four.
(*---------ex2----------*)
Lemma le_then_O :
  forall n,
    le_Nat n O = true ->
    n = O.
Proof.
    intros.
    destruct n as [|n']eqn:E.
    -reflexivity.
    -inversion H.
Qed.
(*---------ex3----------*)
Lemma le_refl:
  forall x,
    le_Nat x x = true.
Proof.
   induction x.
  -simpl. reflexivity.
  -simpl. rewrite IHx. reflexivity.
Qed.

Lemma le_Trans :
  forall m n p,
    le_Nat m n = true ->
    le_Nat n p = true ->
    le_Nat m p = true.
Proof.
  induction m .
  -intros. simpl. reflexivity.
  -intros. simpl in H. destruct n.
  --inversion H.
  --simpl. destruct p.
  * simpl in H0. exact H0.
  * simpl in H0. apply IHm with ( n := n).
  ** exact H.
  **exact H0.
Qed.
(*---------ex4----------*)
Fixpoint plus (k m : Nat) : Nat :=
  match k with
  | O   => m
  | S n => S (plus n m)
  end.

Lemma x_mai_mic_x_plus_y : 
  forall x y , le_Nat x (plus x y) = true.
Proof.
  intros.
  induction x.
  -simpl. reflexivity.
  -simpl. rewrite IHx. reflexivity.
Qed.
(*---------ex5----------*)
Lemma x_mai_mic_sau_egal_y_implica_x_mai_mic_x_plus_y : 
  forall x y z, le_Nat x y = true -> le_Nat x (plus y z) = true.
Proof.
  induction x.
  -intros. simpl. trivial.
  -intros. simpl in H. destruct y.
  --simpl. inversion H.
  --simpl. apply IHx. exact H.
Qed.

(*---------ex6----------*)
Lemma x_mai_mic_egal_y_atunci_max_xy_este_y : 
    forall x y , le_Nat x y = true -> max x y = y.
Proof.
  induction x.
  -intros. trivial.
  -intros. induction y.
  -- simpl in H. inversion H.
  --simpl. simpl in H. apply IHx in H. rewrite H. reflexivity.
Qed.
(*---------ex7----------*)
Lemma x_not_mic_egal_y_implica_max_x_y_este_x : 
      forall x y ,le_Nat x y = false -> max x y = x.
Proof.
  induction x.
  -intros. simpl in H. inversion H.
  -intros. induction y.
  --simpl. trivial.
  --simpl. simpl in H. apply IHx in H. 
  rewrite H. reflexivity.
Qed.












