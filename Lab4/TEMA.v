Require Import String.
(* Check "a". throws 'Error: No interpretation for string "a".' *)

Open Scope string_scope.
Check "a".
Check  "".
Check "abcb".

(*---------ex1----------*)
Inductive AExp :=
| var : string -> AExp
| num : nat -> AExp
| add : AExp -> AExp -> AExp
| sub : AExp -> AExp -> AExp 
| div : AExp -> AExp -> AExp.


Check (var "x").
Check (num 8).
Check (add (var "x") (num 8)).

Coercion var : string >-> AExp.
Coercion num : nat >-> AExp.

Check (add "x" 8).

Notation "A +' B" := (add A B)
                       (at level 50, left associativity).
Notation "A -' B" := (sub A B)
                       (at level 50 , left associativity).
Notation "A /' B" := (div A B)
                       (at level 40, left associativity).
Check (add (num 2) (add (var "x") (div (num 2) (var "y")))).
Check (add 2 (add "x" (div 2 "y"))).


Set Printing Coercions.
Check (add 2 (add "x" (div 2 "y"))).
Unset Printing Coercions.

Check 2 +' ("x" +' 2 /' "y").
Set Printing All.
Check 2 -' ("x" +' 2 /' "y").
Check 2 -' "x" /' "y".

Check "x" /' "y" +' 2.
Check "x" /' "y" /' "z".
Unset Printing All.
(*------------ex2----------*)

Inductive Cond :=
| base : bool -> Cond
| bnot : Cond -> Cond
| beq  : AExp -> AExp -> Cond
| less : AExp -> AExp -> Cond
| band : Cond -> Cond -> Cond.

Coercion base : bool >-> Cond.

Check (bnot true).



Notation "A <' B" := (less A B)
                      (at level 41, left associativity).
Notation "A =' B" := (beq A B)
                      (at level 44, left associativity).
Notation "A &' B" := (band A B)
                       (at level 50 , left associativity).
Notation "! A " := (bnot A)
                       (at level 49 , left associativity).
Notation "A |' B" := (bnot(band A B))
                       (at level 51 , left associativity).
Notation "A >' B" := (bnot(less A B))
                       (at level 41 , left associativity).

Notation "A <=' B" := ((less A B) |' (beq A B))
                       (at level 41 , left associativity).
Notation "A >=' B" := ((bnot(less A B)) |' (beq A B))
                       (at level 41 , left associativity).


  Set Printing All.

Check "x" <' "y".
Check "x" =' "y".
Check ! "x" =' "y".
Check "x" <' "y" &' "x" =' "y".
Check "x" <' "y" |' "x" =' "y".
Check "x" >' "y" |' "x" =' "y".
Check "x" >' "y".
Check 2 >' "y".
Check 3 >' "y".
Check "x" <=' "y".
Check 3 <=' "y".
Check 2 <=' "y".
Check "x" >=' "y".
Check 2 >=' "y".
Check 1 >=' "y".
Check !(! "x" <' "y" &' ! "x" =' "y").
Check ("x" <' "y" |' "x" =' "y") .

(*----------ex3----------*)

Inductive Stmt :=
| skip : Stmt
| assign : string -> AExp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt
| while : Cond -> Stmt -> Stmt .

(*---------ex4-----------*)

Check (assign "x" ("x" +' 1)).

Notation "A ::= B" := (assign A B) (at level 97, right associativity).
Notation "S1 ;; S2" := (seq S1 S2) (at level 98, right associativity).



Definition compute_modulo (x y : string) :=
  "m" ::= 0 ;;
   while (x >' y) (
      x ::= x -' y
   );;
   ite (x =' y) ("m" ::= 0) ("m" ::= x) ;;
   "result" ::= "m".
Check compute_modulo.

Definition is_even (x : string) :=
  ite (x /' 2 =' 0) ("is_even" ::= 1) ("is_even" ::= 0).
Check is_even.
(*------------ex5-------------*)
(*
  int a,b;
while(a!=b){
  if(a>b) then
    a-=b;
  else
    b-=a;
}
return a;
*)
Definition Euclid (a b : string) :=
    a ::= 30;;
    b ::= 18;;
    "result" ::= 0;;
   while ( a >' b) (
    a ::= a -' b
  );;
   while (b >' a) (
    b ::= b -' a
  );;
   "result" ::= b.
Check Euclid.

(*------------ex6-----------*)
(*
  int fibo(int a){
  a = 1 ;
  b = 1; 
  c = 0;
  for(int i=2; i< n; ++i)
  {
    c = a + b;
    a = b;
    b = c;
  }
  
  return c;
  }
*)
Definition Fibonacci ( n : string) :=
      "a'" ::= 1 ;;
      "b'" ::= 1 ;;
      "c'" ::= 0 ;;
      "result" ::= 0;;
      "i'" ::= 2;;    
while("i'" <' n) (
    "c'" ::= "a'" +' "b'";;
    "a'" ::= "b'";;
    "b'" ::= "c'"
  );;
   "result" ::= "c'".
 (*s1 ;; s2 ;; s3*)
Check Fibonacci.











