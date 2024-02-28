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