(* ex1  *)
Inductive BinaryTree (A : Type) : Type :=
  | Leaf : BinaryTree A
  | Node : A ->BinaryTree A -> BinaryTree A ->BinaryTree A.

Arguments Node {A}.
Arguments Leaf {A}.
Check Node 3 Leaf. 

(* ex 2 *)

Fixpoint size {A : Type}
            (tree : BinaryTree A) : nat :=
  match tree with
  | Leaf => 0
  | Node _ l r => 1 + size l + size r
 end.

Definition exemple_tree : BinaryTree nat :=
 Node 1 (Node 2 Leaf Leaf) (Node 3 (Node 4 Leaf Leaf) Leaf).

Compute size exemple_tree.

(* ex 3 *)

Fixpoint height {A : Type}
      (tree : BinaryTree A) : nat:=
  match tree with
  |Leaf => 0
  |Node _ l r => 1 + max(height l) ( height r)
end.

(* ex4*)

Require Import Lia.

Definition has_one_digit (n: nat) := Nat.leb n 9.
Check has_one_digit.

Definition height_leb_size { A : Type }
                (tree : BinaryTree A) : bool :=
    Nat.leb(height tree)(height tree).

Compute height_leb_size(exemple_tree).

Require Import Nat.

Lemma max_lr :
  forall a b, max a b = a \/ max a b  = b.
Proof.
 induction a as [|a'].
  -simpl. right. reflexivity.
  -intros. simpl. destruct b.
  *left. reflexivity.
  *assert (H: max a' b = a' \/ max a' b = b). apply IHa'.
  destruct H. 
  **rewrite H. left. reflexivity.
  **rewrite H. right. reflexivity.
Qed.
Lemma a_less_ab :
  forall a b c,
    a <=? b = true ->
    a <=? b + c = true.
Proof.
  induction a.
  -simpl. reflexivity.
  -simpl. intros.
     destruct b; intros; simpl.
      inversion H.
apply IHa. trivial.
Qed.

Lemma a_less_cb :
  forall a b c,
    a <=? b = true ->
    a <=? c + b = true.
Proof.
  intros.
  assert (h1 : c + b = b + c).
  lia.
  rewrite h1.
  apply a_less_ab.
  trivial.
Qed.

Lemma height_mai_mic_decat_size : 
      forall A : Type , 
      forall tree : BinaryTree A ,
     height tree <=? size tree = true.
Proof.
    induction tree as [|tree'].
    -simpl. reflexivity.
    -simpl. 
     assert (Hmax :  max (height tree1) (height tree2) =
     height tree1 \/ max (height tree1) (height tree2) =
     height tree2).
      apply max_lr.
      destruct Hmax as [Hmax | Hmax].
      * rewrite Hmax. apply a_less_ab. exact IHtree1.
      * rewrite Hmax. apply a_less_cb. exact IHtree2.
Qed.

(*ex5*)

Check list.
Require Import List.
Import ListNotations.
Fixpoint flatten { A : Type}
    ( tree : BinaryTree A)
    ( f : A -> A) : list A :=
    match tree with 
    | Leaf => []
    | Node x l r => [f x] ++ (flatten l f) ++ (flatten r f)
   end.


Compute flatten exemple_tree (fun x=> x+2).

