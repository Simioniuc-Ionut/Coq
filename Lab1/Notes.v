Inductive Nat :=
| O : Nat         (* zero *)
| S : Nat -> Nat. (* succ *)

Check(S(S O)).

Inductive ListNat:=
| Nil : ListNat
| Cons: Nat ->ListNat -> ListNat.

Compute (Cons (S O ) Nil).