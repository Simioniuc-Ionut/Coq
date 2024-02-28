(* le_Nat transitivity *)

Inductive Nat := O | S : Nat -> Nat.

Fixpoint le_Nat (m n : Nat) : bool :=
  match m with
  | O => true
  | S m' => match n with
            | O => false
            | S n' => le_Nat m' n'
            end
  end.

Lemma trans :
  forall m n p,
    le_Nat m n = true ->
    le_Nat n p = true ->
    le_Nat m p = true.
Proof.
  (* intros m n p Hmn Hnp. *)
  induction m.
  - simpl. reflexivity.
  - intros n p Hmn Hnp.
    simpl.
    destruct p as [| p'].
    + simpl in Hmn.
      destruct n as [| n'].
      * exact Hmn.
      * simpl in Hnp. exact Hnp.
    + simpl in Hmn.
      destruct n as [| n'].
      * discriminate Hmn.
      * simpl in Hnp.
        apply IHm with (n := n'); assumption.
Qed.

(* nat in Coq *)
Check nat.
Print nat.
Check 0.
Require Import Nat.
Check add.

Compute add 2 4.
Compute 2 + 4.
Compute 2 =? 4.
Compute 2 <=? 4.
Compute 5 <? 4.

(* Polymorphic types *)
(* Inductive ListNat := *)
(* | Nil : ListNat *)
(* | Cons : nat -> ListNat -> ListNat. *)

(* Check (Cons 2 Nil). *)
(* Check (Cons 3 (Cons 2 Nil)). *)
(* Check (Cons 6 (Cons 3 (Cons 2 Nil))). *)

(* Inductive ListBool := *)
(* | Nil' : ListBool *)
(* | Cons' : bool -> ListBool -> ListBool. *)

Inductive List (T : Type) :=
| Nil : List T
| Cons : T -> List T -> List T.

Check List.
Check Nil.
Check Cons.

Check Nil nat.
Check Cons nat 3 (Nil nat).
Check Cons nat 5 (Cons nat 3 (Nil nat)).

(* implicit arguments *)
Arguments Nil {T}.
Arguments Cons {T}.
Check Nil.
Check Cons 3 Nil.
Check Cons 5 (Cons 3 Nil).

Fixpoint length {T : Type}
         (l : List T) : nat :=
  match l with
  | Nil       => 0
  | Cons x xs => 1 + length xs
  end.

Compute length (Cons 5 (Cons 3 Nil)).

Definition ListNat := List nat.

(* lists in Coq *)
Require Import List.

Print list.
Import ListNotations.
Check nil.
Check [].
Check [1].
Check [2; 5].

(* nil === [] *)
(* cons ===    _ :: _ *)
Check cons 2 [].
Check 2 :: [].

Compute nth 10 [10;20;30] 0.

(* High-order functions *)
Fixpoint filter {T : Type}
         (l : list T)
         (f : T -> bool) : list T :=
  match l with
  | []      => []
  | x :: xs => if (f x)
               then x :: filter xs f
               else filter xs f
  end.

Check even.
Compute even 2.
Compute even 101.
Compute filter [1;5;3;56;78;3;35] even.

(* Lambda-functions *)

Check (fun n => n <=? 50). (* lambda functii *)

Compute filter [1;5;3;56;78;3;35] (fun n => n <=? 50).

(* option types *)
Check option.
Print option.

Check (Some 3).
Check None.

Definition subtraction
           (m n : nat) : option nat :=
  if (m <? n)
  then None
  else Some (m - n).

Compute subtraction 4 5.
Compute subtraction 4 4.            
Compute subtraction 5 4.


(* Compose *)
Definition compose {A B C : Type}
           (f : A -> B)
           (g : B -> C) : A -> C  :=
  fun x => g (f x).

Check compose.

Check compose
        (fun x => x + 1)
        (fun x => x * x).
        
Compute compose
        (fun x => x + 1)
        (fun x => x * x) 100.

Compute compose
        (fun x => x * x)
        (fun x => x + 1) 100.

(* Prop *)
Print bool.
Check true.
Check false.

Check True.
Check False.

Locate "&&".
Compute andb true false.

Check Prop.

Check 10 = 10.
Check 10 = 11.

Goal 10 = 10.
  reflexivity.
Qed.

Goal 10 = 11.
Proof.
  (* can't prove this *)
Abort.

Compute 10 = 10.

(* theorems *)
Theorem and_elim_1:
  forall (A B : Prop), A /\ B -> A.
Proof.
  intros A B H.
  destruct H as [HA HB].
  exact HA.
Qed.

Theorem and_elim_2:
  forall (A B : Prop), A /\ B -> B.
Proof.
  intros A B H.
  destruct H as [HA HB].
  exact HB.
Qed.

Lemma equiv :
  forall (P Q R : Prop),
    (P -> Q -> R) <-> ((P /\ Q) -> R).
Proof.
  intros P Q R.
  split.
  - intros H. intros PQ.
    apply H.
    apply and_elim_1 in PQ. assumption.
    apply and_elim_2 in PQ. assumption.
  - intros PQR HP HQ.
    apply PQR.
    split; assumption.
Qed.

Theorem and_intro:
  forall (A B : Prop), A -> B -> (A /\ B).
Proof.
  intros.
  split; assumption.
Qed.
  
Theorem or_elim:
  forall (A B C: Prop),
    (A -> C) ->
    (B -> C) ->
    (A \/ B) -> C.
Proof.
  intros.
  destruct H1 as [H1 | H1].
  - apply H. assumption.
  - apply H0. assumption.
Qed.
  
Theorem or_intro_1:
  forall (A B : Prop), A -> (A \/ B).
Proof.
  intros.
  left.
  assumption.
Qed.

  
Theorem or_intro_2:
  forall (A B : Prop), B -> (A \/ B).
Proof.
  intros.
  right.
  assumption.
Qed.
  

Theorem not_not:
  forall (P : Prop), P -> ~~P.
Proof.
  intros.
  Locate "~".
  unfold not.
  intros.
  apply H0.
  assumption.
Qed.

  
Theorem mp :
  forall A B,
    (A -> B) -> A -> B.
Proof.
  intros.
  apply X.
  assumption.
Qed.

  
Theorem mt :
  forall (A B : Prop),
    (A -> B) -> ~ B -> ~ A.
Proof.
  intros.
  unfold not in *.
  intros.
  apply H0.
  apply H.
  assumption.
Qed.