Inductive Season :=
|  Winter
|  Spring
|  Summer
|  Fall.

Check Winter.

Definition next_season(s : Season) : Season :=
  match s with
|Winter => Spring
|Spring => Summer
|Summer =>Fall
|Fall=> Winter
end.
Check next_season.

Compute (next_season Summer).