(*Inductive Byte :=
| byte : B->B->B->B->B->B->B->B->Byte.

Inductive Pair :=
| mypair :B->B->Pair.

Definition addbit(b1 b2: B) : Pair :=
  match

https://tinyurl.com/lab2-plp

Definition is_even' (i : nat) : bool :=
 if i mod 2 == 0
  then true
else false.


Require Import Arith.

Check Nat.div.
*)
Inductive B :=
| c : bool->bool->bool->B.
Check c true false false.

(*Definition add_B (b1 b2 : B) : B :=
 match b1,b2 with
| c u2 u1 u0,c v2 v1 v0 => 
   let (mypair cr0 bb0) := addbit u0 v0 in 
   let (mypair cr1 bb1) := addbit u1 v1 in
   let (mypair cr2 bb2) := addbit u2 v2 in 
   c
     get_second (addbit bb2 get_first(addbit bb1 cr0)) 
     get_second (addbit bb1 cr0)
 
match addbit u0 v1 with
  mypair p0 q0=>
*)
Definition add_three_B (b1 b2 cr ) :B :=
match b1,b2 with
| c u2 u1 u0,c v2 v1 v0 => 
  let (mypair cr0 , bb0) := addbit u0 vo myfaulse in
  let (mypair cr1 bb1) := addbit u1 v1 cr0 in
  let (mypair cr2 bb2) := addbit u2 v2 cr1 in 
  c bb2 bb1 bb0.

Definition t :=
| let (c bb1 bb0 v) := (c true true true).
