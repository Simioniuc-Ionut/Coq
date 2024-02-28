Require Import String.
(*----EX1----*)
Inductive E :=
| O : E
| S : E->E
| isZero : E->E
| T : E
| F : E
| ite : E->E->E->E.

Inductive small_eval:
      E->E->Prop :=
| eSucc  :  forall e1 e1',
      small_eval e1 e1' ->
      small_eval (S e1) (S e1')
| e_IsZero_O :
  small_eval (isZero O) T
| e_IsZero_S : forall e1,
  small_eval (isZero (S e1)) F
| e_IsZero_small_eval :forall e1 e1' ,
    small_eval e1 e1' ->
    small_eval (isZero e1) (isZero e1')
| e_ITE_True : forall e1 e2 ,
      small_eval(ite T e1 e2) e1
| e_ITE_False : forall e1 e2,
      small_eval(ite F e1 e2) e2
| e_ITE_Cond : forall e1 e1' e2 e3 e2' e3',
      small_eval e1 e1' ->
      small_eval e2 e2' ->
      small_eval e3 e3' ->
      small_eval(ite e1 e2 e3)(ite e1' e2' e3').
Notation "E1 --> E2" := (small_eval E1 E2)(at level 40).

Inductive Typ : Type :=
| Nat
| Bool.

Inductive type_of : E -> Typ -> Prop :=
| t_zero: 
    type_of O Nat
| t_succ: forall n,
    type_of n Nat -> 
    type_of (S n) Nat
| t_isZero: forall n,
    type_of n Nat -> 
    type_of (isZero n) Bool
| t_true: type_of T Bool
| t_false: type_of F Bool
| t_ite: forall e1 e2 e3,
    type_of e1 Bool ->
    type_of e2 Nat ->
    type_of e3 Nat -> 
    type_of (ite e1 e2 e3) Nat.

(*----EX2----*)
(*           .
TZero ------------
        O : Nat

         e : Nat
TSucc -------------
        S e : Nat

          e : Nat
TisZero -------------
        isZero e : bool

            .
TTrue ------------
         T : bool
            .
TFalse ------------
         F : bool

      e1 : bool   e2 : Nat  e3 : Nat
Tite --------------------------------
          ite e1 e2 e3 : Nat*)

(*Daca tipul lui E este Nat.*)

(*----EX3----*)
(*
    
  1)                           .
                       TZero---------
            .                O : Nat
  TTrue ----------    TSucc----------
        T : bool         (S O) : Nat
  Tite --------------------------------
          ite T (S O) O : Nat
                                  .
  2)                       TZero-------
               .                O : Nat
     TFalse----------  TSucc--------------
           F : bool          (S O)  : Nat
     Tite --------------------------------
          ite F O (S O)  : Nat
  3)
                   .
           TZero-------
                 O : Nat
       TisZero--------------
           isZero O : bool
*)
(*Daca E trece in Nat.*)

Example e1:
    type_of(ite T  (S O)  O) Nat.
Proof.
  eapply t_ite.
  -apply t_true.
  -apply t_succ.
  apply t_zero.
  -apply t_zero.
Qed.
Example e2: 
      type_of (ite F  O (S O)) Nat.
Proof.
    apply t_ite.
     -apply t_false.
     -apply t_zero.
     -apply t_succ. apply t_zero.
Qed.
Example e3:
     type_of (isZero O) Bool.
Proof.
    apply t_isZero.
    apply t_zero.
Qed.
(*----EX4----*)
(**)

Inductive nat_value : E -> Prop :=
| nat_val : forall n, nat_value  (S n).

Inductive b_value : E -> Prop :=
| b_true : b_value T
| b_false : b_value F.

Definition value (e : E) :=
nat_value e \/ b_value e.

Lemma bool_canonical :
forall e, type_of e Bool ->
value e ->
b_value e.
Proof.
    intros e H1 H2.
    inversion H2;trivial.
    inversion H;subst. inversion H1.
Qed.  
Lemma nat_canonical :
  forall e , type_of e Nat ->
  value e -> nat_value e.
Proof.  
  intros e H H1.
  inversion H1; trivial.
  inversion H.
  -subst. inversion H0. 
  -subst. inversion H0.
  -subst. inversion H0.
Qed.
#[local] Hint Constructors nat_value : type_of.
#[local] Hint Constructors b_value : type_of.
#[local] Hint Unfold value : type_of.


Theorem progress :
  forall t T ,
  type_of t T ->
  value t \/ exists t', t --> t'.
Proof.
  intros t H H'.
  induction H; eauto with type_of.
   -apply nat_canonical in H'; eauto with type_of; inversion H';
  eauto with type_of ; subst; 
  apply nat_canonical in H'; inversion H'.  
   +apply nat_canonical in H'. inversion H'.
 
   
Theorem preservation :
forall t T t',
type_of t T ->
t --> t' ->
type_of t' T.
Proof.
 intros t T t' Htype Hstep.
 revert t' Hstep.
 induction Htype; intros t' H';inversion H'; subst; eauto with type_of.
  -
