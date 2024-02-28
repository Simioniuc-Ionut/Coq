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
