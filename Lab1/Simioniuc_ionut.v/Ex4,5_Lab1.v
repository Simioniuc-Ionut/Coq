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
