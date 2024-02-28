Inductive Nat :=
| O : Nat         (* zero *)
| S : Nat -> Nat. (* succ *)

Check(S(S O)).

Fixpoint addition (n  m : Nat) : Nat :=
  match n with
|  O     => m
| (S n') => S (addition n'  m)
end.

Compute addition (S O) (S(S O)).

Fixpoint subtraction (n m : Nat) : Nat :=
  match n , m with
|  O    ,  _     => O
| (S n'),  O     => (S n')
| (S n'), (S m') => subtraction n' m'
end.

Compute subtraction (S (S O)) (S (S O)) .

Print bool.
Fixpoint is_even( n  : Nat) : bool :=
 match n with
| O         => true
| (S O)     => false
| (S(S n')) => is_even n'
end.

Fixpoint multiply(n m : Nat) : Nat :=
  match n, m with
| O , _ => O
| _ , O => O
| (S n'), (S m') => addition m (multiply n' m)
end.

Compute multiply (S(S (S O))) (S(S (S O))).

Fixpoint is_greater_or_equal (n m : Nat) : bool :=
  match n, m with
  (* Cazurile de bază *)
  | _, O => true (* Dacă n este 0, atunci m este mai mare sau egal *)
  | O, _ => false (* Dacă m este 0, atunci n nu este mai mare sau egal *)
  | (S n'), (S m') => is_greater_or_equal n' m'
end.

Fixpoint division(d,i : Nat) : Nat :=
  match d,i with
| _ , O => O (*cazurile de baza*)
| O , _ => O
| (S n'), (S O) => (S n')
  if is_greater_or_equal d i then
     (*Impartire cu numaratorul mai mare decat numitor
      trebuie si de verificat daca numitorul se imparte exact la numarator,
      altfel o sa avem rest...*)
 else
    (*impartirea cu rest*)
end.



