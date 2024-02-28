
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

Coercion var : string >-> AExp.
Coercion num : nat >-> AExp.

Check (add "x" 8).

Notation "A +' B" := (add A B)
                       (at level 50, left associativity).
Notation "A *' B" := (mul A B)
                       (at level 40, left associativity).
(* environment *)
Definition Env := string -> nat.

Definition env0 : Env :=
  fun n => if string_dec n "x"
           then 7
           else if string_dec n "y"
           then 10
           else 0.
Compute env0 "x".
Compute env0 "y".
Compute env0 "z". 

Definition update
           (x : string)
           (v : nat)
           (e : Env)
  : Env :=
  fun y => if string_dec y x
           then v
           else e y.

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

Inductive BExp :=
| btrue  : BExp
| bfalse : BExp
| bnot   : BExp -> BExp
| band   : BExp -> BExp -> BExp
| blt    : AExp -> AExp -> BExp
| bgt    : AExp -> AExp -> BExp.
Check bool.
Compute negb true.
Check Nat.ltb.
Check Nat.leb.

Fixpoint beval (b : BExp) (e : Env) : bool :=
  match b with
  | btrue      => true
  | bfalse     => false
  | bnot b'    => negb (beval b' e)
  | band b1 b2 => if (beval b1 e)
                  then (beval b2 e)
                  else false
  | blt a1 a2  => Nat.ltb (aeval a1 e) (aeval a2 e)
  | bgt a1 a2  => negb (Nat.leb (aeval a1 e)
                                (aeval a2 e))
  end.

Check btrue.
Check bnot btrue.
Check blt "x" 10.

Notation "A <' B" := (blt A B) (at level 60).
Notation "A >' B" := (bgt A B) (at level 60).
(* Notation "A &&' B" := (band A B) (at level 81, left associativity). *)
Infix "&&'" := band (at level 81, left associativity).

Inductive Stmt :=
| assign : string -> AExp -> Stmt
| ite : BExp -> Stmt -> Stmt -> Stmt
| skip : Stmt
| seq : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt.

Notation "A :=' B" := (assign A B) (at level 97, right associativity).
Notation "S1 ;; S2" := (seq S1 S2) (at level 98, right associativity).

Fixpoint eval
         (s : Stmt)
         (e : Env)
         (fuel : nat)
  : Env :=
  match fuel with
  | 0 => e
  | S n =>
      match s with
      | assign x a  => update x (aeval a e) e 
      | ite c s1 s2 => if (beval c e)
                       then eval s1 e n
                       else eval s2 e n
      | skip        => e
      | seq s1 s2   => eval s2 (eval s1 e n) n
      | while c s   => if (beval c e)
                       then
                         (eval
                            (s ;; while c s) e n)
                       else e
      end
  end.

(*Big_step semantics*)
(*
  Const     ------------
        < i , e > => < i >

 Lookup--------------------
        <x , e > => < e(x) >

       <a1 , e > => <i1> <a2 , e > => <i2>
  Add -----------------------
      <a1 +' a2 ,e > => <i1 + i2>
      
     <a1 , e > => <i1> <a2 , e > => <i2>
  Mul-------------------------
      <a1 *' a2 , e> => <i1*i2>
*)

Reserved Notation "A =[ E ] => N" (at level 60).

(*definesc o relatie,nu o funcite*)

Inductive Aeval : AExp -> Env -> nat -> Prop:=
| Const :forall i e, num i =[e] => i
| Lookup:forall x e, var x =[e] => e x
| Add:forall a1 a2 i1 i2 e n,
  a1 =[e] => i1 ->
  a2 =[e] => i2 ->
  n  = i1 + i2 ->
  a1 +' a2 =[e] =>n
| Mul:forall a1 a2 i1 i2 e ,
  a1 =[e] => i1 ->
  a2 =[e] => i2 ->
  a1 *' a2 =[ e ] => i1 * i2
where "A =[ E ] => N" := (Aeval A E N).

Compute env0 "n".

Example Aeval_ex1 :
 2 +' "n" =[env0] => 2 + 0.
Proof.
 apply Add with (i1:=2)(i2 :=0).
 -apply Const.
 -apply Lookup.
  -reflexivity.
Qed.

Example Aeval_ex2 :
 2 +' "n" =[env0] => 2.
Proof.
 apply Add with (i1 := 2) (i2 := 0).
 -apply Const.
 -apply Lookup.
 -simpl;reflexivity.
Qed.
 
Example Aeval_ex3:
  2 +' "n" =[env0] =>2.
Proof.
 eapply Add.
 -apply Const.
 -apply Lookup.
 -unfold env0.
  simpl.
  reflexivity.
Qed.


(* auto / eauto *)
#[local] Hint Constructors Aeval : mydb.
#[local] Hint Unfold env0 : mydb.
#[local] Hint Unfold update : mydb.


Example Aeval_ex4:
  2 +' "n" =[env0] =>2.
Proof.
  eauto with mydb.
Qed.

Reserved Notation "B ={ E } => V" (at level 70).
Print BExp.

Inductive Beval : BExp -> Env -> bool -> Prop :=
| T : forall e, btrue ={e} => true
| F : forall e, bfalse ={e} => false
| notTrue : forall b e,
    b ={e} => true ->
    bnot b ={e} => false
| notFalse : forall b e,
    b ={e} => false ->
    bnot b ={e} => true
| andTrue : forall b1 b2 e,
    b1 ={e} => true ->
    b2 ={e} => true ->
    band b1 b2 ={e} => true
| andFalse : forall b1 b2 e,
    b1 ={e} => false ->
    band b1 b2 ={e} => false
| lt : forall i1 i2 a1 a2 e,
    a1 =[e] => i1 ->
    a2 =[e] => i2 ->
    blt a1 a2 ={e} => Nat.ltb i1 i2
| gt : forall i1 i2 a1 a2 e,
    a1 =[e] => i1 ->
    a2 =[e] => i2 ->
    bgt a1 a2 ={e} => Nat.ltb i2 i1
where "B ={ E } => V" := (Beval B E V).



#[local] Hint Constructors Beval : mydb.
#[local] Hint Unfold env0 : mydb.
#[local] Hint Unfold update : mydb.

(*
Example beval_ex1:
 2 +' "n" <' 10 ={ env0 } => true.
Proof.
 eauto.
Qed.
*)
Reserved Notation "S -[ E ]-> I" (at level 99).
Print Stmt.

Inductive Eval : Stmt -> Env -> Env-> Prop :=
| Assign : forall a e v e' x,
  a =[ e ] => v ->
  e' = update x v e ->
  assign x a -[e]-> e'
| Skip : forall e , skip -[ e ]-> e
| Seq : forall s1 s2 e e1 e2,
  s1 -[ e ]-> e1 ->
  s2 -[ e1 ]-> e2 ->
  seq s1 s2 -[ e ]-> e2
| WhileF : forall b e s,
  b ={ e }=> false ->
  while b s -[ e ]-> e
| WhileT : forall b e s e',
   b ={ e }=> true ->
   s ;; while b s -[ e ]-> e' ->
   while b s -[ e ]-> e'
| IfT : forall b e s1 s2 e',
   b ={ e } => true ->
   s1 -[ e ]-> e' ->
   ite b s1 s2 -[ e ]-> e'
| IfF : forall b e s1 s2 e',
  b ={ e }=> false ->
  s2 -[ e ]-> e' ->
  ite b s1 s2 -[ e ]-> e'
where "S -[ E ]-> I" := (Eval S E I).

Example stmt_1:
  "x" :=' 10 -[ env0 ]-> update "x" 10 env0.
Proof.
  eapply Assign.
  -apply Const.
  -reflexivity.
Qed.

#[local] Hint Constructors Eval : mydb.
#[local] Hint Unfold env0 : mydb.
#[local] Hint Unfold update : mydb.

Require Import Coq.Classes.RelationClasses.


Example step_1:
 "i" :=' 0 ;; while ("i" <'1)
            (
             "i":=' "i" +' 1
            ) -[ env0 ]->
      update"i" 1(update "i" 0 env0).
Proof.
  eauto 10 with mydb.
  eapply Seq. 
  - eapply Assign.
    + apply Const.
    +reflexivity.
   -eapply WhileT. 
    +simpl. apply lt with (i1 := 0) (i2 := 1).
      * apply Lookup.
      * apply Const.
    +eapply Seq.
      *eapply Assign.
        **eapply Add.
          ***apply Lookup.
          ***apply Const.
          ***simpl. reflexivity.
        **reflexivity.
     *eapply WhileF.
       **apply lt with (i1 := 1) (i2 := 1). 
          ***apply Lookup.
          ***apply Const.
Qed.

Print step_1.

(*Aeval - relatie = specificatia bigstep pentru expresii*)
(*aeval - functie de evaluare; interpretor pentru expresii*)

Print Eval.
Theorem a_correct:
 forall a e,
    Aeval a e (aeval a e).
Proof.
  induction a; intros.
    -apply Lookup.
    -apply Const.
    -eapply Add.
      +apply IHa1.
      +apply IHa2.
      +simpl. trivial.
    -eapply Mul.
      +apply IHa1.
      +apply IHa2.
Qed.

Example step_2:
 "i" :=' 0 ;; while ("i"<'2)
            (
             "i" :=' "i" +' 1
            ) -[ env0 ]->
      update"i" 2(update "i" 1( update "i" 0 env0)).
Proof.
  eapply Seq.
   -eapply Assign.
    +apply Const.
    +simpl. reflexivity.
   -eapply WhileT.
    +simpl. apply lt with (i1 :=0 ) (i2 := 1).
      *apply Lookup.
     
Qed.

Print step_2.