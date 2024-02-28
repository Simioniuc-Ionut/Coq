
(* 
IMP: simple imperative language
- expresii aritmetice + variabile
- expresii booleene
- instructiuni: atribuiri, 
  instr decizionale, bucle, blocuri 
de instructiuni + blocuri vide

*)


Require Import String.
Check String.
(* Check "a". *)
Open Scope string_scope.
Check "a".


(* 
Expresii aritmetice: 
variabila
numar natural
adunare
inmultire 
 *)

Inductive AExp :=
| var : string -> AExp
| num : nat -> AExp
| add : AExp -> AExp -> AExp
| mul : AExp -> AExp -> AExp.


Check (var "x").
Check (num 8).
Check (add (var "x") (num 8)).

Coercion var : string >-> AExp.
Coercion num : nat >-> AExp.

Check (add "x" 8).

Notation "A +' B" := (add A B)
                       (at level 50, left associativity).
Notation "A *' B" := (mul A B)
                       (at level 40, left associativity).
Check "x" +' 8 *' "y".
Set Printing All.
Check "x" +' 8 *' "y".


Check "z" *' 10 +' "p".

Unset Printing All.

(*< "x" | -> 7 ; "y" | -> 10 >*)

(*environmnet*)

Definition Env := string->nat.

Definition env0 : Env :=
  fun v => if string_dec v "x"
            then 7
            else if string_dec v "y"
            then 10
            else 0.
Compute env0 "x".
Compute env0 "y".
Compute env0 "z".
            

Definition update 
        (x : string ) 
        (v : nat ) 
        (e : Env)
 : Env :=
fun y => if string_dec y x
          then v
          else e  y.

Definition empty_env := fun _:string => 0.

Definition env1 : string -> nat := 
    (update "x" 7 empty_env).

Compute env1 "x".
Compute env1 "y".

Definition env2 : Env :=
    (update "y" 10 env1).

Compute env2 "y".
Compute env2 "x".

Fixpoint aeval (a : AExp) (e : Env) : nat :=
  match a with
  | num v => v
  | var x => e x
  | add a1 a2 => (aeval a1 e) + (aeval a2 e)
  | mul a1 a2 => (aeval a1 e) * (aeval a2 e)
end.

Compute aeval ("x" +' 8 *' "y") env2.


(* Expresii booleene:
 - true si false
 - negatii
 - conjunctii
 - mai mic strict
 - mai mare strict 
 *)

Inductive BExp :=
| btrue  : BExp
| bfalse : BExp
| bnot   : BExp -> BExp
| band   : BExp -> BExp -> BExp
| blt    : AExp -> AExp -> BExp
| bgt    : AExp -> AExp -> BExp.

Compute negb true.
Check Nat.ltb.

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

Check btrue.
Check bnot btrue.
Check blt "x" 10.

Notation "A <' B" := (blt A B) (at level 60).
Notation "A >' B" := (bgt A B) (at level 60).

Check "x" <' 10.

Compute beval ("x" <' 10) env2.
Compute beval ("y" <' 10) env2.


(* Notation "A &&' B" := (band A B) (at level 81, left associativity). *)
Infix "&&'" := band (at level 81, left associativity).

Compute beval("x" <' 10 &&' "y" <' 11) env2.

Set Printing All.
Check "x" <' 10 &&' "n" >' 0.
Unset Printing All.



(* Statements: 
- atribuiri: "x" :=' "x" +' 1
- structuri decizionale: 
    ite "n" >' 0 ("x" :=' "x" +' 1) ("x" :=' "x" *' 1)
- bucle: while ("n" >' 0) "x" :=' "x" +' 1
- blocuri: "x" :=' "x" +' 1 ;; "x" :=' "x" +' 1 
 *)

Inductive Stmt :=
| assign : string -> AExp -> Stmt
| ite : BExp -> Stmt -> Stmt -> Stmt
| skip : Stmt
| seq : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt.


Check (assign "x" ("x" +' 1)).

Notation "A :=' B" := (assign A B) (at level 97, right associativity).
Notation "S1 ;; S2" := (seq S1 S2) (at level 98, right associativity).


Check "x" :=' "x" +' 1.

Check ite ("n" >' 0) (
                     "x" :=' "x" +' 1
                   )
                   ( 
                     "x" :=' "x" *' 1
                   ).


Check "i" :=' "i" +' 1 ;;
            "sum" :=' "sum" +' "i".


Definition PGM_SUM :=
  "n" :=' 10 ;;
  "i" :=' 0 ;;
  "sum" :=' 0 ;;
  while ("i" <' "n") (
    "i" :=' "i" +' 1 ;;
    "sum" :=' "sum" +' "i"
  ).
Check PGM_SUM.
(*evaluam programe,programele sunt defintie cu statemant, Stmt*)
(*returnez efectul pe care il are programul/stmt asupra unui env,si retunrez env,*)
Fixpoint eval 
      (s : Stmt) 
      (e: Env) 
      (fuel: nat)
      : Env :=  
  match fuel with 
  | 0   => e
  | S n =>
         match s with
         | assign x a  => update x (aeval a e) e (*(aeval a e) = un value, valoarea lui a in env respectiv*)
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

Unset Printing All.
Compute (eval 
               ("n" :=' 10 ;;
                "i" :=' 7  ;;
                ite ("n" <' "i")
                    ("min" :=' "n")
                    ("min" :=' "i") 
                )
               empty_env 10) "min".

Print PGM_SUM.
Compute (eval
         PGM_SUM
         empty_env 30)
          "sum".
(*functiile sunt relatii dar nu si invers
  o functie are asociat un singur element din codomeniu pt  elemntul di domeniu,acelea 
sunt relatii.
*)


Definition SUM (n : nat):=
  "n" :=' n ;;
  "i" :=' 0 ;;
  "sum" :=' 0 ;;
  while ("i" <' "n") (
    "i" :=' "i" +' 1 ;;
    "sum" :=' "sum" +' "i"
  ).

         

(*n = adancimea subarborelui de executie*)
Compute (eval
         (SUM 2)
         empty_env 2000)
          "sum".

Compute (eval
         (SUM 3)
         empty_env 2000).

(*Big_step semantics*)
