Inductive Nat := O : Nat | S : Nat -> Nat.

Definition one := S O.
Definition two := S one.
Definition three := S two.
Definition four := S three.
Definition five := S four.

Fixpoint eq_Nat (n m : Nat) :=
  match n, m with
  | O, O       => true
  | O, S _     => false
  | S _, O     => false 
  | S n', S m' => eq_Nat n' m'
end.

Compute eq_Nat O O.
Compute eq_Nat one O.
Compute eq_Nat one one.
Compute eq_Nat one four.
Compute eq_Nat five four.
Compute eq_Nat five five.

Fixpoint add (m n : Nat) : Nat :=
  match m with
  | O => n
  | S m' => S (add m' n)
  end.

Compute add one one.
Compute add one five.
Compute add five one.
Compute add five O.
Compute add O five.

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















