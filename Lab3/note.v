Inductive Nat := 
| O : Nat 
| S : Nat -> Nat.


Fixpoint le_Nat (m n : Nat) : bool :=
  match m ,n with
  | O , _         => true 
  | _ , O         => false  
  | (S m'),(S n') => le_Nat m' n'
end.

Lemma le_Trans :
  forall m n p ,
  le_Nat m n = true ->
  le_Nat n p = true ->
  le_Nat m p = true.
Proof.
   induction m.
  -intros n p Hn Hp.
   simpl. reflexivity.
  -intros n p Hn Hp.
    simpl.
    destruct p as [|p'].
    *simpl in Hn.
      destruct n as [|n'].
    +exact Hn.
    +simpl in Hp. exact Hp.
    *simpl in Hn.
      destruct n as [|n'].
    **inversion Hn.
    **simpl in Hp. apply IHm with (n :=n').
    *** exact Hn.
    ***exact Hp.
Qed.

Theorem and_elim_1:
  forall (A B : Prop), A /\ B -> A.
Proof.
  