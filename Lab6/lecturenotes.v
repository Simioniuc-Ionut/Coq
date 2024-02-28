(*4.1.1 ,Define an environment that returns values different from 0 for all
the program variables occuring in the sum program below:,*)
 
Require Import String.
Open Scope string_scope.

Inductive Aexp :=
| var : string ->Aexp
| num : nat ->Aexp
| add : Aexp -> Aexp -> Aexp
| mul : Aexp -> Aexp -> Aexp.

Coercion num :  nat >-> Aexp.
Coercion var :  string >-> Aexp.
Check  1.
Check add 1 2.

Notation "A +' B" := (add A B)
                        (at level 50,left associativity).
Notation "A *' B" := (mul A B)
                        (at level 45, left associativity).
Definition Env := string -> nat.

Definition sigma1 : Env :=
 fun v =>  if string_dec v "n"
          then 10
          else if string_dec v "s"
          then 0
          else if string_dec v "i"
          then 0
          else 1.

Check var "n".

Inductive BExp :=
| btrue  : BExp
| bfalse : BExp
| bnot   : BExp -> BExp
| band   : BExp -> BExp -> BExp
| blt    : Aexp -> Aexp -> BExp
| bgt    : Aexp -> Aexp -> BExp.

Fixpoint aeval (a : Aexp) (e : Env) : nat :=
  match a with
  | num v => v
  | var x => e x
  | add a1 a2 => (aeval a1 e) + (aeval a2 e)
  | mul a1 a2 => (aeval a1 e) * (aeval a2 e)
end.


Fixpoint beval (b : BExp) (e : Env) : bool :=
  match b with 
  | btrue      => true
  | bfalse     => false
  | bnot b'    => negb(beval b' e)
  | band b1 b2 => if(beval b1 e)
                  then (beval b2 e)
                  else false
  (*exemplu de optimizare pt andb*)
  | blt a1 a2  => Nat.ltb (aeval a1 e) (aeval a2 e) 
  | bgt a1 a2  => negb (Nat.leb (aeval a1 e)
                                (aeval a2 e))
end.


Notation "A <' B" := (blt A B) (at level 60).
Notation "A >' B" := (bgt A B) (at level 60).

Check "x" <' 10.


Inductive Stmt :=
| assign : string -> Aexp -> Stmt
| ite : BExp -> Stmt -> Stmt -> Stmt
| skip : Stmt
| seq : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt.


Check (assign "x" ("x" +' 1)).

Notation "A ::= B" := (assign A B) (at level 97, right associativity).
Notation "S1 ;; S2" := (seq S1 S2) (at level 98, right associativity).

Definition PGM_SUM :=
 "n" ::= 10  ;;
 "s" ::= 0  ;;
 "i" ::= 0  ;;

  while("i" <' "n" +' 1) (
        "s" ::= "s" +' "i" ;;
        "i" ::= "i" +' 1 
    ).
Check PGM_SUM.

Print option.

Definition Env' := string -> option nat.
Definition sigma1' := fun var => if(string_dec var "n")
                                 then Some 10
                                 else if (string_dec var "i")
                                        then Some 0
                                        else None.
Compute sigma1' "n".
Compute sigma1' "i".
Compute sigma1' "Deci nu vrea?".
(*am declarat alt env*)
Definition update 
        (v : nat ) 
        (x : string )  
        (e : Env)
 : Env :=
fun y => if string_dec y x
          then v
          else e  y.
Definition sigma2 := update 11 "n" sigma1.
Compute sigma2 "n".
Compute sigma2 "s".


Definition update'(env : Env')(var : string)(val : option nat) : Env' :=
 fun x => if(string_dec var x)
             then val
             else (env x).
Definition sigma2' := update' sigma1' "n" (Some 12).
Compute sigma2' "n".
Compute sigma2' "x".
(*----eval for arithmetic-------*)

(*e scris mai sus*)

Compute aeval ("n" +' 2 *' "n") sigma1.
Compute aeval ("n" +' 2 *' "n") sigma2.

Definition empty_env := fun _:string => 0.

Definition env1 : string -> nat := 
    (update 7 "n" empty_env  ).

Compute env1 "n".
Compute env1 "y".

Fixpoint eval (s:Stmt)(e : Env)(fuel : nat): Env :=
  match fuel with
 | 0   => e
 | S n => 
          match s with 
          | assign x a => update (aeval a e) x e
          | ite c s1 s2 => if (beval c e)
                           then eval s1 e n
                           else eval s2 e n
          | skip        => e (*daca excut blocul vid de instructiuni raman cu environment,*)
          | seq s1 s2   => eval s2 (eval s1 e n) n
          | while c s   => if (beval c e) 
                         then (eval 
                                 (s ;; while c s) e n)
                                    (*am adaugat un parametru fuel care sa mi limiteze nr de executii*)
                         else e
       end
end.
Definition SUM (n : nat):=
  "n" ::= n ;;
  "i" ::= 0 ;;
  "sum" ::= 0 ;;
  while ("i" <' "n") (
    "i" ::= "i" +' 1 ;;
    "sum" ::= "sum" +' "i"
  ).

Definition sum_env := (eval (SUM 10) empty_env 100).
Compute sum_env "sum".








