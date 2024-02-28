Require Import String.

Inductive Exp :=
| anum : nat -> Exp
| avar : string -> Exp
| aplus : Exp -> Exp -> Exp
| amult : Exp -> Exp -> Exp
| btrue : Exp
| bfalse : Exp
| bnot : Exp -> Exp
| band : Exp -> Exp -> Exp
| blessthan : Exp -> Exp -> Exp.
                          

Coercion anum : nat >-> Exp.
Coercion avar : string >-> Exp.
Notation "A +' B" := (aplus A B) (at level 50, left associativity).
Notation "A *' B" := (amult A B) (at level 40, left associativity).
Notation "A <' B" := (blessthan A B) (at level 60).
Notation "A &&' B" := (band A B) (at level 71, left associativity).

Check 2 +' 2.
Check 2 +' btrue.
Check 2 &&' 2.

Definition Env := string -> nat.
Definition update
           (sigma : Env)
           (x : string)
           (v : nat) : Env :=
  fun y => if eqb x y
           then v
           else (sigma y).


Reserved Notation "A -[ S ]-> B"
         (at level 90).


Inductive eval :
  Exp -> Env -> Exp -> Prop :=
| const : forall i sigma,
    (anum i) -[ sigma ]-> i
| lookup : forall x sigma,
    (avar x) -[ sigma ]-> (sigma x)
| add_l : forall a1 a2 sigma a1',
    a1 -[ sigma ]-> a1' ->
    (a1 +' a2) -[ sigma ]-> (a1' +' a2)
| add_r : forall a1 a2 sigma a2',
    a2 -[ sigma ]-> a2' ->
    (a1 +' a2) -[ sigma ]-> (a1 +' a2')
| add : forall i1 i2 sigma n,
    n = i1 + i2 -> 
    (i1 +' i2) -[ sigma ]-> n
| mul_l : forall a1 a2 sigma a1',
    a1 -[ sigma ]-> a1' ->
    (a1 *' a2) -[ sigma ]-> (a1' *' a2)
| mul_r : forall a1 a2 sigma a2',
    a2 -[ sigma ]-> a2' ->
    (a1 *' a2) -[ sigma ]-> (a1 *' a2')
| mul : forall i1 i2 sigma n,
    n = i1 * i2 -> 
    (i1 *' i2) -[ sigma ]-> n
| etrue : forall sigma,
  btrue -[ sigma ]-> btrue
| efalse : forall sigma,
  bfalse -[ sigma ]-> bfalse
| lessthan_l : forall a1 a2 sigma a1',
    a1 -[ sigma ]-> a1' ->
    (a1 <' a2) -[ sigma ]-> (a1' <' a2)
| lessthan_r : forall a1 a2 sigma a2',
    a2 -[ sigma ]-> a2' ->
    (a1 <' a2) -[ sigma ]-> (a1 <' a2')
| lessthan_ : forall i1 i2 sigma b,
    b = (if Nat.ltb i1 i2 then btrue else bfalse) -> 
    (i1 <' i2) -[ sigma ]-> b
| not_1: forall b b' sigma,
    b -[ sigma ]-> b' ->
    (bnot b) -[ sigma ]-> (bnot b')
| not_t : forall sigma,
    (bnot btrue) -[ sigma ]-> bfalse
| not_f : forall sigma,
    (bnot bfalse) -[ sigma ]-> btrue
| band_1 : forall b1 b2 b1' sigma,
    b1 -[ sigma ]-> b1' ->
    (band b1 b2) -[ sigma ]-> (band b1' b2)
| band_true : forall b2 sigma,
    (band btrue b2) -[ sigma ]-> b2
| band_false : forall b2 sigma,
  (band bfalse b2) -[ sigma ]-> b2
where "A -[ S ]-> B" := (eval A S B).

Reserved Notation "A -[ S ]>* B"
         (at level 90).
Inductive eval_closure :
  Exp -> Env -> Exp -> Prop :=
| refl : forall e sigma,
    e -[ sigma ]>* e
| tran : forall e1 e2 e3 sigma,
  e1 -[ sigma ]-> e2 ->
  e2 -[ sigma ]>* e3 ->
  e1 -[ sigma ]>* e3      
where "A -[ S ]>* B" :=
  (eval_closure A S B).

Create HintDb types.
#[local] Hint Constructors Exp : types.
#[local] Hint Constructors eval : types.
#[local] Hint Constructors eval_closure : types.

Definition Env0 : Env := fun x => 0.

#[local] Hint Unfold Env0 : types.
#[local] Hint Unfold update : types.


Open Scope string_scope.
Example e1:
  2 +' "n" -[ Env0 ]>* 2.
Proof.
  apply tran with (e2 := 2 +' 0).
  - apply add_r.
    apply lookup.
  - eapply tran.
    + apply add. trivial.
    + simpl. apply refl.
Qed.


Example e1':
  2 +' "n" -[ Env0 ]>* 2.
Proof.
  eauto with types.
Qed.

Example e2:
  "n" +' "n" -[ Env0 ]>* 0.
Proof.
  eauto 10 with types.
Qed.


Example e2':
  2 +' btrue -[ Env0 ]>* btrue.
Proof.
  eauto 10  with types.
Abort.



(* TYPES *)

(* Typ *)
Inductive Typ : Type :=
| Nat
| Bool.
Print Exp.
(* Typing rules *)
Inductive type_of : Exp -> Typ -> Prop :=
| tnum : forall n,
    type_of (anum n) Nat  
| tvar : forall x,
    type_of (avar x) Nat 
| tplus : forall a1 a2,
  type_of a1 Nat ->
  type_of a2 Nat ->
  type_of (a1 +' a2) Nat 
| tmul : forall a1 a2,
  type_of a1 Nat ->
  type_of a2 Nat ->
  type_of (a1 *' a2) Nat 
| ttrue : type_of btrue Bool
| tfalse : type_of bfalse Bool
| tnot : forall b,
  type_of b Bool ->
  type_of (bnot b) Bool
| tand : forall b1 b2,
  type_of b1 Bool ->
  type_of b2 Bool ->
  type_of (band b1 b2) Bool
| tlessthan : forall a1 a2,
  type_of a1 Nat ->
  type_of a2 Nat ->
  type_of (a1 <' a2) Bool.
  
          
#[local] Hint Constructors Typ : types.
#[local] Hint Constructors type_of : types.

(* Examples *)
Example ex10:
  type_of (2 +' "n") Nat.
Proof.
  apply tplus.
  - apply tnum.
  - apply tvar.
Qed.

Example ex10':
  type_of (2 +' "n") Nat.
Proof.
  eauto with types.
Qed.

Example ex11:
  type_of (2 +' btrue) Nat.
Proof.
  eauto with types.
  (* can't prove this *)
Abort.


(* values *)
Inductive nat_value : Exp -> Prop :=
| n_val : forall n, nat_value (anum n).

Inductive bool_value : Exp -> Prop :=
| bt : bool_value btrue
| bf : bool_value bfalse.

Definition value (e : Exp) :=
  nat_value e \/ bool_value e.

#[local] Hint Constructors nat_value : types.
#[local] Hint Constructors bool_value : types.
#[local] Hint Unfold value : types.


(* Bool canonical *)
Lemma bool_canonical :
  forall b,
    type_of b Bool ->
    value b ->
    bool_value b.
Proof.
  intros b H H'.
  inversion H'.
  - inversion H0. subst.
    inversion H.
  - assumption.
Qed.

(* Nat canonical *)
Lemma nat_canonical :
  forall n,
    type_of n Nat ->
    value n ->
    nat_value n.
Proof.
  intros n H H'.
  inversion H'.
  - assumption.
  - inversion H0; subst; inversion H.
Qed.

(* Progress *)
(* TODO *)

(* Preservation *)
(* TODO *)

(* Soundness *)
(* TODO *)