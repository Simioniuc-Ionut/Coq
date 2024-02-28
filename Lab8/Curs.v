Require Import String.
Open Scope string_scope.

Definition Env := string -> nat.
Definition update (env : Env)
           (x : string) (v : nat) : Env :=
  fun y =>
    if (eqb y x)
    then v
    else (env y).

(* arithmetic expressions *)
Inductive AExp :=
| var : string -> AExp
| num : nat -> AExp
| plus : AExp -> AExp -> AExp
| mult : AExp -> AExp -> AExp.

Coercion var : string >-> AExp.
Coercion num : nat >-> AExp.
Notation "A +' B" := (plus A B)
                      (at level 50,
                        left associativity).

Notation "A *' B" := (mult A B)
                      (at level 40,
                        left associativity).

(* Small-step operational semantics *)
Reserved Notation "A =[ S ]=> N" (at level 70).

Inductive aeval_small_step :
  AExp -> Env -> AExp -> Prop :=
| alookup : forall x sigma,
    var x =[ sigma ]=> (sigma x)
| aconst : forall n sigma,
    num n =[ sigma ]=> n
| add_1 : forall a1 a1' a2 sigma,
    a1 =[ sigma ]=> a1' ->
    a1 +' a2 =[ sigma ]=> a1' +' a2
| add_2 : forall a1 a2' a2 sigma,
    a2 =[ sigma ]=> a2' ->
    a1 +' a2 =[ sigma ]=> a1 +' a2'
| add : forall i1 i2 sigma n,
        n = num (i1 + i2) ->
        i1 +' i2 =[ sigma ]=> n   
| mul_1 : forall a1 a1' a2 sigma,
    a1 =[ sigma ]=> a1' ->
    a1 *' a2 =[ sigma ]=> a1' *' a2
| mul_2 : forall a1 a2' a2 sigma,
    a2 =[ sigma ]=> a2' ->
    a1 *' a2 =[ sigma ]=> a1 *' a2'
| mul : forall i1 i2 sigma n,
        n = num (i1 * i2) ->
        i1 *' i2 =[ sigma ]=> n   
where "A =[ S ]=> N" :=
  (aeval_small_step A S N).

Definition Env1 := update (fun x => 0) "n" 10.

Example ex1 : 2 +' "n" =[ Env1 ]=> 2 +' 10.
Proof.
  apply add_2.
  apply alookup.
Qed.

Example ex2 : "n" +' 2 =[ Env1 ]=> 10 +' 2.
Proof.
  apply add_1.
  apply alookup.
Qed.

Example ex3_oups : "n" +' 2 =[ Env1 ]=> 12.
Proof.

Abort.


Reserved Notation "A =[ S ]>* N" (at level 70).
Inductive aeval_closure  :
  AExp -> Env -> AExp -> Prop :=
| a_refl : forall a sigma, a =[ sigma ]>* a
| a_tran : forall a1 a2 a3 sigma,
    (a1 =[ sigma ]=> a2) ->
    (a2 =[ sigma ]>* a3) ->
    (a1 =[ sigma ]>* a3)
where "A =[ S ]>* N" :=
  (aeval_closure A S N).

Example ex3 : "n" +' 2 =[ Env1 ]>* 12.
Proof.
  eapply a_tran.
  - apply add_1.
    apply alookup.
  - eapply a_tran.
    + apply add. simpl. trivial.
    + apply a_refl.
Qed.

Create HintDb d1.
#[local] Hint Constructors aeval_small_step : d1.
#[local] Hint Constructors aeval_closure : d1.

#[local] Hint Unfold Env1 : d1.
#[local] Hint Unfold update : d1.

Example ex3' : "n" +' 2 =[ Env1 ]>* 12.
Proof.
  eauto with d1.
Qed.

Print Env1.
Definition Env2 := update Env1 "m" 12.

Example ex4 : "n" +' "m" =[ Env2 ]>* 22.
Proof.
  apply a_tran with (a2 := 10 +' "m" ).
  - apply add_1.
    apply alookup.
  - apply a_tran with (a2 := 10 +' 12).
    + apply add_2.
      apply alookup.
    + apply a_tran with (a2 := 22).
      * apply add. simpl. reflexivity.
      * apply a_refl.
Qed.

Example ex4' : "n" +' "m" =[ Env2 ]>* 22.
Proof.
  eauto 10 with d1.
Qed.

(* boolean expressions *)
Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| blessthan : AExp -> AExp -> BExp
| bgreaterthan : AExp -> AExp -> BExp.

Notation "! A" := (bnot A) (at level 70).
Notation "A &&' B" := (band A B) (at level 76, left associativity).
Notation "A <' B" := (blessthan A B) (at level 65).
Notation "A >' B" := (bgreaterthan A B) (at level 65).

Reserved Notation "B ={ Sigma }=> B'"
         (at level 90).

Inductive beval_small_step :
  BExp -> Env -> BExp -> Prop :=
| lessthan_1 : forall a1 a1' a2 sigma,
    a1 =[ sigma ]=> a1' ->
    a1 <' a2 ={ sigma }=> a1' <' a2
| lessthan_2 : forall i1 a2' a2 sigma,
    a2 =[ sigma ]=> a2' ->
    (num i1) <' a2 ={ sigma }=> (num i1) <' a2'
| lessthan : forall i1 i2 b sigma,
    b = (if Nat.ltb i1 i2 then btrue else bfalse) ->
    (num i1) <' (num i2) ={ sigma }=> b
| greaterthan_1 : forall a1 a1' a2 sigma,
    a1 =[ sigma ]=> a1' ->
    a1 >' a2 ={ sigma }=> a1' >' a2
| greaterthan_2 : forall i1 a2' a2 sigma,
    a2 =[ sigma ]=> a2' ->
    (num i1) >' a2 ={ sigma }=> (num i1) >' a2'
| greaterthan : forall i1 i2 b sigma,
    b = (if negb (Nat.leb i1 i2) then btrue else bfalse) ->
    (num i1) >' (num i2) ={ sigma }=> b
| not : forall b b' sigma,
    b ={ sigma }=> b' ->
    (bnot b) ={ sigma }=> (bnot b')
| not_true : forall sigma,
    (bnot btrue) ={ sigma }=> bfalse
| not_false : forall sigma,
    (bnot bfalse) ={ sigma }=> btrue
| and_1 : forall b1 b1' sigma b2,
    b1 ={ sigma }=> b1' ->
    (band b1 b2) ={ sigma }=> (band b1' b2)
| and_false : forall b2 sigma,
    (band bfalse b2) ={ sigma }=> bfalse
| and_true : forall b2 sigma,
    (band btrue b2) ={ sigma }=> b2
where "B ={ S }=> B'" := (beval_small_step B S B').

Reserved Notation "B ={ S }>* B'" (at level 90).

Inductive beval_closure : BExp -> Env -> BExp -> Prop :=
| b_refl : forall b sigma,
    b ={ sigma }>* b
| b_tran : forall b1 b2 b3 sigma,
    (b1 ={ sigma }=> b2) ->
    (b2 ={ sigma }>* b3) ->
    (b1 ={ sigma }>* b3)
where "B ={ S }>* B'" := (beval_closure B S B').

Example ex5 : 1 +' 3 <' 5 ={ Env1 }>* btrue.
Proof.
  (* TODO *)
Admitted.
     
#[local] Hint Constructors beval_small_step:d1.
#[local] Hint Constructors beval_closure:d1.


Example ex5' : 1 +' 3 <' 5 ={ Env1 }>* btrue.
Proof.
  eauto 10 with d1.
Qed.


(* Statements *)
Inductive Stmt :=
| skip : Stmt
| assignment : string -> AExp -> Stmt
| ite : BExp -> Stmt -> Stmt -> Stmt
| seq : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt.

Notation "S1 ;; S2" := (seq S1 S2)
                         (right associativity,
                           at level 99).
Notation "X ::= A" := (assignment X A) (at level 95).

Reserved Notation "St1 -{ State }->[ St2 ; State' ]"
         (at level 100).

Inductive eval_small_step :
  Stmt -> Env -> Stmt -> Env -> Prop :=
| assign_2 : forall a a' x sigma,
    a =[ sigma ]=> a' -> 
    (x ::= a) -{ sigma }->[ x ::= a' ; sigma ]
| assign : forall x i sigma,
    (x ::= (num i)) -{ sigma }->[ skip ; update sigma x i ]
| sequence_1 : forall s1 s1' s2 sigma sigma',
    s1 -{ sigma }->[ s1' ; sigma' ] ->
    (s1 ;; s2) -{ sigma }->[ s1' ;; s2 ; sigma' ]
| sequence : forall s2 sigma,
    (skip ;; s2) -{ sigma }->[ s2 ; sigma ]
| if_1 : forall b b' s s' sigma,
    b ={ sigma }=> b' ->
    ite b s s' -{ sigma }->[ ite b' s s' ; sigma ]
| if_true : forall s s' sigma,
    ite btrue s s' -{ sigma }->[ s ; sigma ]
| if_false : forall s s' sigma,
    ite bfalse s s' -{ sigma }->[ s' ; sigma ]
| while_ : forall b s sigma, 
     (while b s) -{ sigma }->[ ite b (s ;; while b s) skip  ; sigma ]
where "St1 -{ State }->[ St2 ; State' ]" := (eval_small_step St1 State St2 State').

Reserved Notation "St1 -{ State }>*[ St2 ; State' ]"
         (at level 100).
Inductive eval_closure : Stmt -> Env -> Stmt -> Env -> Prop :=
| refl : forall s sigma, s -{ sigma }>*[ s ; sigma ]
| tran : forall s1 s2 s3 sigma1 sigma2 sigma3,
    s1 -{ sigma1 }->[ s2 ; sigma2 ] ->
    s2 -{ sigma2 }>*[ s3 ; sigma3 ] -> 
    s1 -{ sigma1 }>*[ s3 ; sigma3 ]
where "St1 -{ State }>*[ St2 ; State' ]" :=
  (eval_closure St1 State St2 State').


Example ex6 :
  ("x" ::= 10) -{ Env1 }>*[ skip ; update Env1 "x" 10].
Proof.
(* TODO *)
Admitted.

Compute Env1 "n".

Example ex7 :
  ("x" ::= "n") -{ Env1 }>*[ skip ; update Env1 "x" 10].
Proof.
  (* TODO *)
Admitted.

#[local] Hint Constructors eval_small_step : d1.
#[local] Hint Constructors eval_closure : d1.


Example ex6' :
  ("x" ::= 10) -{ Env1 }>*[ skip ; update Env1 "x" 10].
Proof.
  eauto with d1.
Qed.


Example ex7' :
  ("x" ::= "n") -{ Env1 }>*[ skip ; update Env1 "x" 10].
Proof.
  eauto with d1.
Qed.


Example ex7'' :
  ("x" ::= "n") ;; ("x" ::= 11) -{ Env1 }>*[ skip ; update (update Env1 "x" 10) "x" 11].
Proof.
  eauto 10 with d1.
Qed.