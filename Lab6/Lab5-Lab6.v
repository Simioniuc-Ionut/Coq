(*Abstract syntax *)

Inductive Exp : Type :=
|num  : nat->Exp
|add  : Exp->Exp->Exp
|mul : Exp->Exp->Exp.

Check (num 1).
Check (num 2).
Check (add(num 1)(num 2)).

Coercion num : nat >-> Exp.

Check 1.
Check (add 1 2).

Notation "X +^ Y" := (add X Y ) (at level 50, left associativity).
Notation "X *^ Y" := (mul X Y ) (at level 40, left associativity).


Set Printing All.
Check 1 +^ 2 .
Unset Printing All.

(*-----parteaa de sintaxa peste bool,aritmetics si programs -----*)
Require Import String.

Inductive AExp :=
|avar  : string -> AExp
|anum  : nat    -> AExp
|aplus : AExp   -> AExp
|amul  : AExp   -> AExp.
Coercion anum : nat >-> AExp.
