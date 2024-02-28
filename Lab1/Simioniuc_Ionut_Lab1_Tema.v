(*_____ex3________*)
Inductive Day :=
| Monday
| Tuesday
| Wednesday
| Thursday
| Friday
| Saturday
| Sunday.

Definition next_day (d : Day) : Day :=
  match d with 
| Monday    => Tuesday
| Tuesday   => Wednesday
| Wednesday => Thursday
| Thursday  => Friday
| Friday    => Saturday
| Saturday  => Sunday
| Sunday    => Monday
end.

Check next_day.

Compute next_day (Sunday).
(*______________ex4.5_________*)
Inductive boolean :=
| true
| false.

Definition negation (n : boolean) : boolean :=
  match n with
| true  => false
| false => true
end.

Definition disjunction (a  b : boolean) : boolean :=
  match a , b with
| true  , true  => true
| true  , false => true
| false , true  => true
| false , false => false
end.

Definition conjunction (a  b : boolean) : boolean :=
  match a , b with 
| true  , false => false
| false , true  => false
| false , false => false
| true  , true  => true
end.

Compute negation true.
Compute disjunction true false.
Compute conjunction false true.

(*_______ex6______*)

Inductive B :=
| mytrue
| myfalse.

Inductive Byte :=
| byte : B->B->B->B->Byte.

Check byte mytrue mytrue mytrue mytrue.
Inductive Pair :=
| mypair :B->B->Pair
| my3pair:B->B->B->Pair.

Definition addbit(b1 b2 : B) : Pair :=
  match b1,b2 with 
| mytrue   , myfalse    =>mypair  mytrue myfalse 
| myfalse  , myfalse    =>mypair  myfalse myfalse
| mytrue   , mytrue     =>my3pair  mytrue myfalse myfalse
| _ , _ => mypair myfalse myfalse
end.

(*Definition add_three_B (b1 b2 cr : B ) : Pair :=*)


(*_________ex6_____facut cu nr naturale*)
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

Fixpoint is_even( n  : Nat) : boolean :=
 match n with
|  O         => true
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

Fixpoint is_greater_or_equal (n m : Nat) : boolean :=
  match n, m with
  (* Cazurile de bază *)
  | _, O => true (* Dacă n este 0, atunci m este mai mare sau egal *)
  | O, _ => false (* Dacă m este 0, atunci n nu este mai mare sau egal *)
  | (S n'), (S m') => is_greater_or_equal n' m'
end.

Fixpoint division( d  i : Nat) : Nat :=
  match d,i with
| _ , O => O (*cazurile de baza*)
| O , _ => O
| (S n'), (S O) => (S n')
  if (is_greater_or_equal d i )then
    (*Impartire cu numaratorul mai mare decat numitor
      trebuie si de verificat daca numitorul se imparte exact la numarator,
      altfel o sa avem rest...*)
 else
    (*impartirea cu rest,pt numitor mai mic decat numarator*)
end.















