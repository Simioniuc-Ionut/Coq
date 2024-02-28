Require Import String.
Open Scope string_scope.
Require Import Lia.
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

Inductive Exp :=
| num : nat -> Exp
| var : string -> Exp
| add : Exp -> Exp -> Exp
| sub : Exp -> Exp -> Exp
| div : Exp -> Exp -> Exp.

Coercion num : nat >-> Exp.
Coercion var : string >-> Exp.

Notation "A +' B" := (add A B)
                       (at level 50, left associativity).
Notation "A -' B" := (sub A B)
                       (at level 50, left associativity).
Notation "A /' B" := (div A B)
                       (at level 40, left associativity).

(*-----------ex1-----------*)

Fixpoint aeval (a : Exp) (env : Env) : option nat :=
  match a with
  | num n => Some (n)
  | var v => Some (env v)
  | add a1 a2 => match aeval a1 env with (*(2/0)+3*)
                 |None => None
                 |Some a1' =>match aeval a2 env with
                             | Some a2' =>Some(a1' + a2')
                             | None => None
                             end
                 end
  | sub a1 a2 => match aeval a1 env with
                 |None => None
                 |Some a1' => match aeval a2 env with
                              |None => None
                              |Some a2' => if(Nat.ltb a1' a2')
                                            then None
                                            else Some(a1' - a2')
                              end
                  end 
  | div a1 a2 => match aeval a2 env with
                 |None => None
                 |Some 0 => None
                 |Some a2' => match aeval a1 env with
                                |None=>None
                                |Some a1' =>Some (Nat.div a1' a2')
                                end
                 end
  end.


Reserved Notation "A =[ E ] => N" (at level 60).

Inductive Aeval : Exp -> Env -> nat -> Prop :=
| Const:  forall n e,  num n =[e] =>n
| Lookup: forall x e,  var x =[e] =>e x
| Add: forall a1 a2 n1 n2 e n,
   a1 =[e] => n1 ->
   a2 =[e] => n2 ->
    n = n1 + n2  ->
   a1 +' a2 =[e] => n
| Sub: forall a1 a2 n1 n2 e n,
   a1 =[e] => n1 ->
   a2 =[e] => n2 ->
     n2 <= n1 ->
    n = n1 - n2  ->
   a1 -' a2 =[e] => n
| Div: forall a1 a2 n1 n2 e n,
   a1 =[e] => n1 ->
   a2 =[e] => n2 ->
   n = Nat.div n1 n2 ->
   n2 <> 0  ->
   a1 /' a2 =[e] => n
 where "A =[ E ] => N" := (Aeval A E N).

Example Aeval_ex1_sub:
 2 -' "n" =[env0] => 2 - 0.
Proof.
  eapply Sub.
  -apply Const.
  -apply Lookup.
  -unfold env0. simpl. lia.
  - simpl. reflexivity.
Qed.
Example Aeval_ex2_sub:
 (3 -' 1) -' "x" =[env0] => (3-1) - 7.
Proof.
  eapply Sub.
  - simpl. unfold env0. eapply Sub.
    + apply Const.
    + apply Const.
    + simpl. lia.
    + simpl. reflexivity.
  - apply Lookup.
  - unfold env0. simpl. Abort.  (*7<2 fals *)

Example Aeval_ex1_div:
 (15/'2) -' 7 =[env0] => (Nat.div 15 2) - 7.
Proof.
 eapply Sub.
 - eapply Div.
   + apply Const.
   + apply Const.
   + simpl. reflexivity.
   + lia.
  -apply Const.
  -simpl.  reflexivity.
  -simpl. reflexivity.
Qed.
Print env0.

Example Aeval_ex2_div:
    3/'"n" =[ env0 ]=> 0.
Proof.
    eapply Div.
    -apply Const.
    -apply Lookup.
    -simpl. unfold env0. reflexivity.
    -Abort. (*n<>0 imposibil*)

(*----------ex2----------*)
Inductive Cond :=
| base : bool -> Cond
| bnot : Cond -> Cond
| beq  : Exp -> Exp -> Cond 
| less : Exp -> Exp -> Cond
| bor : Cond -> Cond -> Cond.
(*| base b    => if(b)
                 then Some (true)
                 else Some (false)*)
Notation "A <' B" := (less A B) (at level 60).
Notation "! A" := (bnot A) (at level 65).
Notation "A =' B" := (beq A B) (at level 60).
Infix "A ||' B" := (bor A B) (at level 81, left associativity).


Reserved Notation "C ={ Sigma } => B" (at level 90).
Print Cond.

Inductive Beval : Cond -> Env -> bool -> Prop :=
  | Btrue : forall b sigma, base b  ={ sigma }=> true
  | Bfalse : forall b sigma, base b ={ sigma }=> false
  | NotT : forall B sigma,
    B ={ sigma }=> true ->
    !B ={ sigma }=> false 
  | NotF : forall B sigma,
    B ={ sigma }=> false ->
    !B ={ sigma }=> true
  | orTrue : forall b1 b2 e,
      b1 ={e} => true ->
      bor b1 b2 ={e} => true
  | orFalse : forall b1 b2 e,
      b1 ={e} => false ->
      b2 ={e} => false ->
      bor b1 b2 ={e} => false
  | Lt1 : forall a1 (a2 : Exp) (i1 : nat)  b sigma, 
    a1 =[ sigma ]=> i1 ->
    (i1 <' a2) ={ sigma }=> b ->
    a1 <' a2 ={ sigma }=> b
  | Lt2 : forall (a2 : Exp) (i1 : nat) i2 b sigma,
    a2 =[ sigma ]=> i2 ->
    b  = Nat.ltb i1 i2 ->
    i1 <' a2 ={ sigma }=> b 
  | Eq : forall a1 a2 i1 i2 b sigma, 
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b  = Nat.eqb i1 i2 ->
    a1 =' a2 ={ sigma }=> b 
 where "C ={ Sigma } => B" := (Beval C Sigma B).



(*--------ex3-------*)
Inductive Stmt :=
| skip : Stmt 
| assign : string -> Exp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt (* if-then-else *)
| it  : Cond -> Stmt -> Stmt (* if-then *)
| dowhile : Stmt -> Cond -> Stmt.

Notation "S1 ;; S2" := (seq S1 S2) (right associativity, at level 99).
Notation "X ::= A" := (assign X A) (at level 95).

Definition update
           (x   : string)
           (v   : nat)
           (env : Env)          
             :
  (string -> nat) :=

  fun y => if eqb y x
           then v
           else (env y).

Reserved Notation "S -[ E ]-> E'"(at level 99).

Inductive eval : Stmt -> Env -> Env -> Prop:=
| Skip : forall e e',
     skip -[ e ]-> e'
| Assign : forall X a e e' i,
      a =[ e ] => i ->
      e' = update X i e ->   
     (X ::= a) -[ e ]-> e'
| Seq : forall s1 s2 sigma sigma0 sigma',
    s1 -[ sigma ]-> sigma0 ->
    s2 -[ sigma0 ]-> sigma' ->
   (s1 ;; s2) -[ sigma ]-> sigma'
| IteTrue : forall B e e' s1 s2,
       B ={ e } => true ->
       s1 -[ e ]-> e' ->  
     (ite B s1 s2) -[ e ]-> e'
| IteFalse : forall B e e' s1 s2,
       B ={ e } => false ->
       s2 -[ e ]-> e' ->
     (ite B s1 s2) -[ e ]-> e'
| ItTrue : forall B e e' s,
       B ={ e } => true ->
       s -[ e ]-> e' ->
      (it B s) -[ e ]-> e'
| ItFalse : forall B e e' s,
       B ={ e } => false ->
      (it B s) -[ e ]-> e'
| DoWhileTrue : forall B e e' s,
       B ={ e } => true ->
       (s ;; dowhile s B) -[ e ]-> e' ->
    (dowhile s B) -[ e ]-> e'
| DoWhileFalse : forall B e e' s,
       B ={ e } => false ->
       s -[ e ]-> e' ->
    (dowhile s B) -[ e ]-> e'
where "S -[ E ]-> E'" := (eval S E E').
#[local] Hint Constructors eval : mydb.

Example sk:
it ("i" <' 1) (skip) -[ env0 ]-> env0.
Proof.
  (*eauto 10 with mydb.*)
   -eapply ItTrue.
    + eapply Lt1. 
      *apply Lookup.
      *eapply Lt2.
       **apply Const.
       **unfold env0. simpl. unfold Nat.ltb. simpl. reflexivity.
    +apply Skip.
Qed.

Example assigment:
"i"::=0 -[ env0 ]-> update "i" 0 env0.
Proof.
 (*eauto with mydb*)
  eapply Assign.
   -apply Const.
   -simpl. reflexivity.
Qed.

Example sequence:
  ("n" ::= 0 ;;( "n" ::= "n" +' 1))
  -[ env0 ]-> update "n" 1 (update "n" 0 env0).
Proof.
  (*eauto with mydb.*)
  eapply Seq.
    -eapply Assign.
      +apply Const.
      +simpl. reflexivity.
    -eapply Assign.
      +eapply Add.
        *apply Lookup.
        *apply Const.
        *simpl. reflexivity.
     +reflexivity.
Qed.
Example if_then_else_false:
  ("n" ::= 1 ;;
  ite ("n" <' 1) ( "n" ::= "n" +' 1)(skip))
  -[ env0 ]-> update "n" 1 (update "n" 0 env0).
Proof.
   eapply Seq. 
     -eapply Assign.
      +apply Const.
      +reflexivity.
    -eapply IteFalse.
      +eapply Lt1.
        *apply Lookup.
        *eapply Lt2. 
          **apply Const.
          ** reflexivity.
      +eapply Skip.
Qed.

Example if_then_else_true:
  ("n" ::= 0 ;;
  ite ("n" <' 1) ( "n" ::= "n" +' 1)(skip))
  -[ env0 ]-> update "n" 1 (update "n" 0 env0).
Proof.
  (*eauto 10 with mydb.*)
  eapply Seq.
    -eapply Assign.
      +apply Const.
      +reflexivity.
    -eapply IteTrue.
      +eapply Lt1.
        *apply Lookup.
        *eapply Lt2. 
          **apply Const.
          ** reflexivity.
      +eapply Assign.
        *eapply Add.
          --apply Lookup.
          --apply Const.
          --reflexivity.
       *simpl. reflexivity.
Qed. 
Example if_then_False:
  ("n" ::= 1 ;;
  it ("n" <' 1) ( "n" ::= "n" +' 1))
  -[ env0 ]-> update "n" 1 (update "n" 0 env0) .
Proof.
    eapply Seq.
   -eapply Assign.
    +apply Const.
    +reflexivity.
  -eapply ItFalse.
    +eapply Lt1.
      *apply Lookup.
      *eapply Lt2.
        **apply Const.
        **unfold update. simpl. unfold Nat.ltb. simpl. reflexivity.
Qed.
Example if_then_True:
  ("n" ::= 0 ;;
  it ("n" <' 1) ( "n" ::= "n" +' 1))
  -[ env0 ]-> update "n" 1 (update "n" 0 env0) .
Proof.
  (*eauto 10 with mydb.*)
  eapply Seq.
   -eapply Assign.
    +apply Const.
    +reflexivity.
  -eapply ItTrue.
    +eapply Lt1.
      *apply Lookup.
      *eapply Lt2.
        **apply Const.
        **unfold update. simpl. unfold Nat.ltb. simpl. reflexivity.
    +eapply Assign.
      *eapply Add.
       **apply Lookup.
       **apply Const.
       **simpl. reflexivity.
      *reflexivity.
Qed.
Example dowhileTrue:
 ("i" ::= 0 ;; 
            dowhile (
             "i" ::= "i" +' 1
            )
          ("i"<'1))
       -[ env0 ]->update"i" 2(update "i" 1( update "i" 0 env0)).
Proof.
   eapply Seq.
     -eapply Assign.
      +apply Const.
      +reflexivity.
    -eapply DoWhileTrue.
      +eapply Lt1.
        *apply Lookup.
        *eapply Lt2.
         **apply Const.
         **unfold update. simpl. unfold Nat.ltb. simpl. reflexivity.
      +eapply Seq.
        *eapply Assign.
          **eapply Add.
           ***apply Lookup.
           ***apply Const.
           ***reflexivity.
          **reflexivity.
        *eapply DoWhileFalse.
         **eapply Lt1. 
          ***simpl. apply Lookup.
          ***simpl. eapply Lt2.
           ****apply Const.
           ****unfold update. simpl. unfold Nat.ltb. simpl. reflexivity.
         **eapply Assign.
          ***eapply Add.
            ****simpl. apply Lookup.
            ****simpl. apply Const.
            ****simpl. reflexivity.
            ***simpl. reflexivity.
Qed.
(*
(*Exercise 5.11.1 Prove that the evaluation of arithmetic expressions is deterministic*)
Lemma aeval_is_deterministic:
 forall a sigma n n', 
    a =[ sigma ]=>n->
    a =[ sigma ]=>n'->
    n=n'.
Proof.                    
   intros a sigma n n' H1.
    generalize dependent n'.
    induction H1; intros n' H2; inversion H2; subst; try reflexivity.
    -f_equal.*)