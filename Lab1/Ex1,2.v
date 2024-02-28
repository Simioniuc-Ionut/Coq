Inductive Day :=
  Monday
| Tuesday
| Wednesday.

Print Day.

Check Monday.

Print bool.
Print nat.

Definition equal (d1 d2 : Day) : bool := 
match d1, d2 with
| Monday    , Monday    => true
| Tuesday   , Tuesday   => true
| Wednesday , Wednesday => true
| _         , _         => false
end.

Compute equal Monday Tuesday.
Compute equal Monday Monday.

Lemma correct_equal :
  