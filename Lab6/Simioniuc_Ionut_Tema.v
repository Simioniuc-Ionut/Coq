
Print option.

Check Some 3.
Check None.

Require Import Nat.
Check Nat.sub.

Compute (Nat.sub 2 3).
Compute (Nat.ltb 2 3).

Require Import String.
Open Scope string_scope.

Definition Env : string ->nat :=
  fun x => if eqb x "n" then 10 else 0.
Compute Env "n".
Compute Env "n1".

Definition update   (env : string->nat) (v : string) (n : nat)
                  : (string -> nat) :=
fun x => if eqb x v then n else (env x).

Compute (update Env "n" 8) "n".
Compute (update Env "n1" 0) "n". (*in env n este 10*) 


(*--------ex1--------*)

Inductive AExp :=
| num : nat -> AExp
| var : string -> AExp
| add : AExp -> AExp -> AExp
| sub : AExp -> AExp -> AExp
| div : AExp -> AExp -> AExp.

Coercion num : nat >-> AExp.
Coercion var : string >-> AExp.

(*
Definition minus' (n m : nat) : option nat :=
 if ltb n m 
 then None
 else Some (Nat.sub n m).

Compute (Nat.sub 4 3).
Compute minus' 4 3.
Compute minus' 2 3.

Definition minus_option (n m : option nat) : option nat :=
 match n , m with
  | Some n' ,Some m' => minus' n' m'
  |_ ,_ =>None
end.

Compute minus_option
  (minus' 2 3)
  (minus' 4 3).

Compute minus_option
      (Some 5) (Some 4).
*)
Check Nat.div.
Check Nat.div 10 2.

Fixpoint aeval(a: AExp) (sigma: string->nat) : option nat :=
  match a with
  |num n    => Some (n)
  |var v    => Some (sigma v)
  |sub a1 a2 => match aeval a1 sigma with
               | None => None
               | Some a1' => match aeval a2 sigma with
                             | None => None
                             | Some a2' => if Nat.ltb a1' a2' 
                                           then None 
                                           else Some(a1' - a2')
                             end
               end
  | add a1 a2 => match aeval a1 sigma with (*este posibil ca unul dintre operanzi sa contina o impartire la zero(ex: ((2/0)+3))*)
               | Some a1' => match aeval a2 sigma with
                             | Some a2' => Some( a1' + a2')
                             | None => None
                              end
               | None => None
               end
  |div a1 a2 => match aeval a2 sigma with
               | None => None
               | Some 0 => None
               | Some a2' => match aeval a1 sigma with
                             | Some a1' => Some ( Nat.div a1' a2')
                             | None => None
                              end
               end
end.


Check option.
Check option nat.
Print option.
Check (Some 2).
Check None.
(*----------ex2---------*)
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
Notation "A |' B" := (bnot(band (bnot A) (bnot B)))
                       (at level 51 , left associativity).
Notation "A >' B" := (bnot(less A B))
                       (at level 41 , left associativity).

Notation "A <=' B" := ((less A B) |' (beq A B))
                       (at level 41 , left associativity).
Notation "A >=' B" := ((bnot(less A B)) |' (beq A B))
                       (at level 41 , left associativity).

Notation "A +' B" := (add A B)
                       (at level 50, left associativity).
Notation "A -' B" := (sub A B)
                       (at level 50 , left associativity).
Notation "A /' B" := (div A B)
                       (at level 40, left associativity).
Check (add (num 2) (add (var "x") (div (num 2) (var "y")))).
Check (add 2 (add "x" (div 2 "y"))).



Inductive Stmt :=
| skip : Stmt 
| assign : string -> AExp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt (* if-then-else *)
| while : Cond -> Stmt -> Stmt.

Check (assign "x" ("x" +' 1)).

Notation "A ::= B" := (assign A B) (at level 97, right associativity).
Notation "S1 ;; S2" := (seq S1 S2) (at level 98, right associativity).



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

Fixpoint eval 
      (s : Stmt) 
      (e : string->nat) 
      (fuel: nat)      
      : string->nat :=
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

(*---------ex3--------*)
Definition Env:= string -> bool.
(*definim cong,disj,negatie si asignarile*)

