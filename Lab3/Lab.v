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
  |Node _ Left Leaf  => 1 + height Left
  |Node _ Leaf Right => 1 + height Right
  |Node _ Left Right => 1 + height Left + height Right
end.

(* ex4*)

Definition has_one_digit (n: nat) := Nat.leb n 9.
Check has_one_digit.









