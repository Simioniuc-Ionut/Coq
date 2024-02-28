Require Import Nat.
Print Nat.

Inductive Nat :=
| o : Nat
| s : Nat->Nat.


(*
IN ALgol60
E -> E
E -> E + E
E -> E * E

IN BNF 
E := E | E + E | E * E

*)
Inductive BT:=
| Leaf  : nat->BT
| Node  : nat->BT->BT->BT. 

Definition tree3 :=
    Node 15
        (Node 10 (Leaf 5) (Leaf 4))
        (Node 4 (Leaf 3) (Leaf 0)).
Check tree3.

Inductive List :=
| Nil : List
| Cons : nat->List->List.
Check (Cons 3 ( Cons 4 Nil)).
Definition L1:= (Cons 3 ( Cons 5 (Cons 1 Nil))).
Definition N1:= (s(s(s o))).
Definition L0:= Nil.
(*2.1.6 last eleemtn*)
Fixpoint last_element (L : List) (N : nat): nat :=
match L with
| Nil => 0 
| Cons n l => match l with
              | Nil => n
              | Cons n' l' => last_element l' n'
              end
end.
Compute last_element L1. 

(*2.1.7*)
Fixpoint number_OF_Nodes (T : BT) : nat :=
  match T with
| Leaf _ => 1
| Node r s1 dr1 => 1 + number_OF_Nodes s1 + number_OF_Nodes dr1
end.
Compute number_OF_Nodes tree3.

(*2.1.10*)
Fixpoint is_even (n : Nat) : bool :=
match n with
| o => true
| (s o) => false
| (s(s n')) => is_even n'
end.
Print N1.
Compute is_even N1.

(*2.1.11*)
Locate "*".
Fixpoint factorial (n : nat) : nat :=
match n with
| O => 0
| (S O) => 1
| (S n') => mul n (factorial n')
end.
Compute factorial 4.

(*2.1.12*)

Fixpoint less2_1_12 (n1 : nat) (n2 : nat) : bool :=
match n1 with
| O => match n2 with
      | O => false      
      | (S n2') => true
      end
| (S n1') => match n2 with 
            | O => false
            | (S n2') => less2_1_12 n1' n2'
            end
end.

Compute less2_1_12 O (S O).
(*2.1.13*)
Theorem plus_o_n :
forall n : nat, plus O n = n.
Proof.
  intros. simpl. reflexivity.
Qed.
(*2.1.15*)
Theorem plus_m_n_plus_n_m : 
 forall n m , m=n ->plus m n = plus n m.
Proof.
  intros. rewrite H. simpl. reflexivity.
Qed.
(*2.1.16*)
Theorem plus_c_a' : 
  forall k , plus k (S O) <> O.
Proof.
  intros.
  unfold not.
  intros.
  destruct k as [|k1'].
  -simpl. inversion H.
  -inversion H.
Qed.
(*2.2.1*)
Theorem plus_n_Sm_is_S_n_m : 
  forall n m , plus n (S m) = S (plus n m).
Proof.
  intros.
  induction n.
  -simpl. reflexivity.
  -simpl. rewrite IHn.  reflexivity.
Qed.
(*Diferentea ce face induction*)
(*cu destruct ,nu ar merge
Theorem plsu_n_O_is_n : 
 forall n , plus n O = n.
Proof.
  destruct n as [|n'].
  -simpl. reflexivity.
  -simpl. rewrite IHn. reflexivity.
Qed.*)
(*cu inductie,iti oferea o ipoteza inductiva
 mai puterncia de care te poti folosi in demonstratea 
goalu lui*)
Theorem plsu_n_O_is_n : 
 forall n , plus n O = n.
Proof.
  induction n.
  -simpl. reflexivity.
  -simpl. rewrite IHn. reflexivity.
Qed.

(*2.2.1*)
Theorem nat_plus_n_Sm_is_S_n_m: 
  forall n m , n + (m + 1) = (n + m) + 1.
Proof.  
  intros.
  induction n.
  -simpl. reflexivity.
  -simpl. rewrite IHn. reflexivity. 
Qed.

(*2.2.4*)
Fixpoint length(l : List) :=
 match l with
| Nil => O
| Cons _ l' => S (length l')
end.
Fixpoint append(l1 l2 : List) :=
match l1 with
| Nil => l2
|Cons x l1' => Cons x (append l1' l2)
end.

Lemma append_len : 
  forall l1 l2, plus(length l1)(length l2) = length(append l1 l2).
Proof.
  induction l1.
  -simpl. reflexivity.
  -simpl. intros. rewrite IHl1. reflexivity.
Qed.
(*Polimorfismul ajuta la scrierea unor functii asemanatoare dar
de tipuri diferite. Foloseste un tip de data Type,care se
refera la tipul pe care il dai tu cand instantiezi functia*)

Inductive ListBool :=
| NilB : ListBool
| ConsB : bool->ListBool->ListBool.
Fixpoint length'(l : ListBool):=
match l with 
| NilB=>O
| ConsB _ l' => S(length' l')
end.
Inductive LList( T : Type ) : Type :=
| Nill  : LList T
| Conss : T -> LList T ->LList T.
Check List.
Check Nill.
Check Conss.
Definition ListNat:= LList Nat.
Check Nill.

Fixpoint length_P(T: Type)(l: LList T) :=
 match l with
| Nill _  => O
| Conss _ _ l' => S (length_P T l')
end.
Compute length_P Nat (Conss Nat o (Nill Nat)).

(*2.3.3*)
Arguments Nill {T}.
Arguments Conss {T}.
Arguments length_P {T}.

Fixpoint repeat {T : Type}(e : T)( n : nat) : LList T :=
 match n with 
| 0 => Nill 
| S n' => Conss e (repeat e n') 
end.

Compute repeat  ListBool 3.
Compute repeat 1 10. 
(* punand T intre {}, nu mai trebui sa ii dau tipul*)
Fixpoint length_P' {T : Type} (L : LList T) : nat :=
match L with
| Nill => 0
| Conss _ L' => 1 + (length_P' L' ) 
end.

(* Exercise 2.3.4 Implement a polymorphic function that concatenates two
lists. Test this function on non-trivial examples. *)

Fixpoint concatenate_list {T : Type } (l1 l2 : LList T) : LList T :=
match l1 with
| Nill => l2
| Conss n l1' => Conss n (concatenate_list l1' l2)
end.
Compute concatenate_list (repeat 2 3) (repeat 0 5).

 (*Exercise 2.3.5 Implement a polymorphic function that reverses a list.*)

Fixpoint reverse_list {T : Type} (l1 : LList T) : LList T :=
match l1 with
| Nill => Nill
| Conss n l1' => match l1' with
                 | Nill => concatenate_list l1' (Conss n Nill)
                 | Conss _ _ =>concatenate_list (reverse_list l1') (Conss n Nill)
                 end
end. 
Compute reverse_list (concatenate_list (repeat 1 3)(repeat 2 4)). 

Fixpoint reverse_list' {T : Type} (l1 : LList T) : LList T :=
match l1 with
| Nill => Nill
| Conss n l' => concatenate_list (reverse_list' l') (Conss n Nill)
end.

Definition list_3 : LList nat := (Conss 1 (Conss 2 (Conss 3 (Conss 4 Nill)))).
Compute reverse_list' ( concatenate_list(repeat 2 3) (repeat 1 1)).
Compute reverse_list list_3.
Require Import Nat.

(*Exercise 2.4.1 Test the function has one digit on several examples.*)
Definition has_one_digit (n : nat) :=
leb n 9.
Compute has_one_digit 2.
Compute has_one_digit 10.
Definition num_list: LList nat := Conss 2 (Conss 15 (Conss 7 (Conss 18 Nill))).

(*2.4.2*)
Fixpoint operation {T : Type }(f : T ->T)(l1 : LList T) : LList T:=
 match l1 with
| Nill => Nill
| Conss x l1' => Conss  (f x) (operation f l1')
end. 

Definition multiply2 (n1 : nat ) : nat :=
n1*2.
Compute operation (multiply2) num_list.
(*scriu numele functiei,apoi in body ul operation cauta numele functiei si ii aplica argumentele respective: f x*)
(*functii anonime == fun n*)
Check (fun n => n  * 2).
(*2.4.3*)
Compute operation (fun n => n  * 2) num_list.
(*functii in functii*)
Definition id {A : Type} {B : Type} (f : A -> B) := f .
Compute (id operation (fun n => 2)) list_3.

Compute has_one_digit 10.
Compute (id has_one_digit ) 10.
Compute has_one_digit 1.
Compute (id has_one_digit ) 1.
Check operation.
Check (id operation).

Definition compose {A :Type} {B:Type} {C:Type} (f : B-> C) (g : A -> B) :=
fun x => f ( g x ).

Check compose.
Check compose (fun x : bool => if x then Nill else (Conss 1 Nill)) (fun x : nat => Nat.leb x 0). 

(*Prop sunt ttipurile care se pot demonstra.*)
Check 10<2.

Lemma simple_conjunction :
  2 + 3 = 5 /\ 5 + 5 = 10.
Proof.
  split.
  -simpl. reflexivity.
  -simpl. reflexivity.
Qed.

Lemma implication_and_conjunction:
  forall n ,n = 0-> n + 3  = 3 /\ n + 5 = 5.
Proof.
  intros n Hn .
  split.
  -rewrite Hn. simpl. reflexivity.
  -rewrite Hn. simpl. reflexivity.
Qed.
Lemma conjunction_as_hypothesis:
  forall n m, n = 0 /\ m = 0 -> n+3=3.
Proof.
  intros n m Hnm.
  destruct Hnm as [Hn Hm].
  -rewrite Hn. trivial.
Qed.
Lemma simple_disjunction': 
  2 + 3 =5 \/ 5+5=11.
Proof.
(*iau arg stang pt ca el este adv*)
  left.
  trivial.
Qed.
Lemma disjunction_as_hypothesis:
  forall n, n =0 \/ 5 + 5 =11 -> n+3 = 3 .
Proof.
  intros n [Hn | Hn].
  rewrite Hn. trivial.
  -inversion Hn.
Qed.
(*    in conjuntii  intros [HN HN] 
  iar in disjunctii intros [Hn|Hn] *)
(*2.5.1*)
Theorem ex_falso : 
  forall P, False->P.
Proof.
  intros .
  inversion H.
Qed.
(*2.5.2*)
Theorem and_elim_1 :
 forall A B : Prop , A /\ B -> A .
Proof.
  intros A B [H1 H2].
  apply H1.
Qed.
(*2.5.3*)
Theorem and_elim_2 :
    forall A B : Prop , A /\ B -> B.
Proof.
  intros A B Hn.
  destruct Hn as [H1 H2].
  apply H2.
Qed.

Theorem and_intro :
  forall (A B : Prop) , A -> B -> (A /\ B) .
Proof.
  intros A B Hn Hm.
  split.
  -apply Hn.
  -apply Hm.
Qed.
(*applic contradict at cand trebuie sa dem ceva fals iar in ipoteza am ceva care implica fals*)
Theorem  not_not:
  forall (P : Prop), P -> ~~P .
Proof.
  intros.
  unfold not. intros. contradict H0. apply H.  
Qed.

(*Chapter 3*)
(*În esență, concret syntax se referă la modul în care 
oamenii scriu codul, în timp ce abstract syntax tree 
reprezintă structura logică abstractă a acelui cod, 
fără a ține cont de detaliile de scriere exactă.*)

(*exercices*)
Require Import String.
Open Scope string.

Inductive AExp :=
| anum   : nat->AExp
| avar   : string->AExp
| aplus  : AExp->AExp->AExp
| amul   : AExp->AExp->AExp 
| adiv   : AExp->AExp->AExp
| amod   : AExp->AExp->AExp
| asub   : AExp->AExp->AExp.

Check aplus (anum 2) (avar "x").
Notation "A +' B" := (aplus A B)
                        (at level 50,left associativity).
Notation "A *' B" := (amul A B)
                        (at level 40,left associativity).
Notation "A /' B" := (adiv A B)
                        (at level 40,left associativity).
Notation "A %' B" := (amod A B)
                        (at level 40,left associativity).
Notation "A -' B" := (asub A B)
                        (at level 50,left associativity).
Check (anum 2) -' (avar "x").
Coercion anum : nat >->AExp.
Coercion avar : string>->AExp.
Check 2 -' "x".

Inductive boolExp :=
| btrue    : boolExp
| bfalse   : boolExp
| bnot     : boolExp -> boolExp
| band     : boolExp -> boolExp -> boolExp
| beq      : AExp -> AExp -> boolExp
| bless    : AExp -> AExp -> boolExp
| bgreater : AExp -> AExp -> boolExp.

Notation "A <' B" := (bless A B)(at level 80).
Notation "A >' B" := (bgreater A B)(at level 80).
Notation "A =' B" := (beq A B)(at level 80).
Infix "&&'" := band (at level 82).
Notation "! A" := (bnot A ) (at level 81).
Notation "A ||' B" := (! (! A &&' !B)) (at level 83).

Check ! "A" <' 2 &&' "C" >' "A".

Inductive Stmt :=
| Assign : string -> AExp -> Stmt
| while  : boolExp -> Stmt -> Stmt
| seq    : Stmt -> Stmt -> Stmt
| forr   : Stmt -> boolExp -> Stmt -> Stmt -> Stmt
| ite    : boolExp -> Stmt -> Stmt -> Stmt
| it     : boolExp -> Stmt -> Stmt.
(* forr (i=1)(i<n)(i++)(
      //codd
    )

*)

Notation "A [=] B" := (Assign A B)(at level 85).
Notation "S1 ;; S2":= (seq S1 S2)(at level 98).

Check "x" [=] 3 ;;
      "y" [=] 10 ;;
      "max" [=] 0 ;;    
     ite ("x" <' "y")
    (
          "max" [=] "y"
    )(
         "max" [=] "x"
    )
.
Check"x" [=] 3 ;;
      "y" [=] 10 ;;
      "max" [=] 0 ;;
       it ("x" <' "y")
    (
          "max" [=] "y"
    )
.
Check "n" [=] 10 ;;
      "i" [=] 0 ;;
      "S" [=] 0;;
      while( "i" <' "n") (
       "S" [=] "S" +' "i";;
       "i" [=] "i" +' 1
      )
.
Check "n" [=] 10;;
    forr("i" [=] 0 ;; "S" [=] 0) ("i" <' "n") ("i" [=] "i" +' 1) (
     "S" [=] "S" +' 1
      )
.
(*Chapter 4*)
(**)
(*un envirnoment = un biding map , [x] [value]*)

Definition Env := string->nat.

Definition sigma1 := fun var => if(string_dec var "x")
                                then 10
                                  else if (string_dec var "i")
                                   then 0
                                   else 0.
Compute sigma1 "n".
Compute sigma1 "i".
Compute sigma1 "daca-i 0 esti fraier".

(*4.1.1 la fel ca sus*)

Definition Env' := string -> option nat.
Definition sigma1' := fun var => if (string_dec var "x")
                                    then Some 10
                                   else if (string_dec var "i")
                                    then Some 0
                                    else None.
Compute sigma1' "n".
Compute sigma1' "i".
Compute sigma1' "daca-i 0 esti fraier".

Definition update (var : string)(val : nat)(env : Env) : Env :=
    fun x => if(string_dec  x var)
              then val
              else (env x).
Definition sigma2 := update "x" 11 sigma1.
Compute sigma2 "x".

(*4.1.3*)
Definition update' (var : string) (val : nat )(env : Env') : Env' :=
  fun x => if(string_dec x var)
          then Some val
          else (env x).
Definition sigma2' := update' "x" 11 sigma1'.
Compute sigma2' "x".
Compute sigma2' "y".

Definition Enver : (string->nat) :=
   fun var => if(string_dec var "x")
              then 11
              else if(string_dec var "y")
              then 12
              else 0.
Compute Enver "x".
Check "x".


(*urmat. sunt evaluatori pentru ahritmetic expressions*)

Fixpoint aeval (a : AExp)(sigma : Env') :option nat:=
  match a with
  | anum n => Some n
  | avar n => (sigma n)
  | aplus x1 x2 => match aeval x1 sigma with
                   | None => None
                   | Some x1' => match aeval x2 sigma with
                                  | None=>None
                                  | Some x2' => Some(x1' + x2')
                                   end
                    end
  | amul x1 x2 => match aeval x1 sigma with
                   | None => None
                   | Some x1' => match aeval x2 sigma with
                                  | None=>None
                                  | Some x2' => Some(x1' * x2')
                                   end
                    end
  | adiv x1 x2 => match aeval x1 sigma with
                   | None => None
                   |(Some 0) => Some 0
                   | Some x1' => match aeval x2 sigma with
                                  | None=>None
                                  | (Some 0) => None
                                  | Some x2' => Some(Nat.div x1' x2')
                                   end
                    end
  | amod x1 x2 => match aeval x1 sigma with
                   | None => None
                   |(Some 0) => Some 0
                   | Some x1' => match aeval x2 sigma with
                                  | None=>None
                                  | (Some 0) => None
                                  | Some x2' => Some(x1' mod x2')
                                   end
                    end
  | asub x1 x2 => match aeval x1 sigma with
                   | None => None
                   |(Some 0) => None
                   | Some x1' => match aeval x2 sigma with
                                  | None=>None
                                  | (Some 0) => Some x1'
                                  | Some x2' => Some(x1' - x2')
                                   end
                    end
end.

Compute aeval ("x" %' 2) sigma1'.
Print boolExp.
Print Nat.eqb.
Fixpoint aeval_nat (a : AExp) (e : Env) : nat :=
  match a with
  | anum v => v
  | avar x => e x
  | aplus a1 a2 => (aeval_nat a1 e) + (aeval_nat a2 e)
  | amul a1 a2 => (aeval_nat a1 e) * (aeval_nat a2 e)
  | adiv a1 a2 => Nat.div (aeval_nat a1 e) (aeval_nat a2 e)
  | amod a1 a2 => (aeval_nat a1 e) mod (aeval_nat a2 e)
  | asub a1 a2 => (aeval_nat a1 e) - (aeval_nat a2 e)

end.
Fixpoint beval (b : boolExp) (env : Env) : bool :=
match b with
| btrue => true
| bfalse => false
| bnot b' => negb (beval b' env)
| band b1 b2 => andb (beval b1 env) (beval b2 env)
| beq  b1 b2 => Nat.eqb (aeval_nat b1 env) (aeval_nat b2 env)
| bless a1 a2 => Nat.ltb (aeval_nat a1 env) (aeval_nat a2 env)
| bgreater a1 a2 => negb (Nat.leb (aeval_nat a1 env) (aeval_nat a2 env))
end.
Print sigma1.
Compute beval ("n" <' "n")sigma1.
Compute beval ("x" >' "i")sigma1.
(*In
contrast, the evaluator for statements returns the environment obtained after the
execution of the statements*)
Print Stmt.
Check "n" [=] 10;;
    forr("i" [=] 0 ;; "S" [=] 0) ("i" <' "n") ("i" [=] "i" +' 1) (
     "S" [=] "S" +' 1
      )
.
Fixpoint eval (s : Stmt) (env : Env) (fuel : nat) : Env :=
  match fuel with
  | 0 => env (* Execuție completă *)
  | S fuel' =>
    match s with
    | Assign x a => update x (aeval_nat a env) env
    | seq s1 s2 => eval s2 (eval s1 env fuel') fuel'
    | while b s1 =>
      if (beval b env) 
       then eval (seq s1 (while b s1)) env fuel'
      else env
    | ite B S1 S2 => if (beval B env)
                     then eval S1 env fuel' 
                      else eval S2 env fuel'
    | it B S1 => if (beval B env )
                then eval S1 env fuel' 
                 else env
    | forr S1 B S2 S3 =>
      eval (seq S1 (while B (seq S3 S2))) env fuel'
    end
  end.

Definition pgm_sum :=
 "n" [=] 10;;
  "i" [=] 1;;
  "sum" [=] 0 ;;
  while("i" <' "n" +' 1)(
  "sum" [=] "sum" +' "i";;
   "i" [=] "i" +' 1  
   ) ;; "result" [=] "sum"
    .
Definition emptysigma := fun _ : string => 0.
Definition sum_env := (eval pgm_sum emptysigma 50).
Compute sum_env  "result".



(*IMP -imperative langague, include Arithmetic,bool ,assign,conditionals,loops and sequences of stmt*)

Reserved Notation "A =[ E ]=> N"(at level 60).
Print AExp.
Inductive aconfig : AExp -> Env -> nat -> Prop :=
| Const : forall n sigma , anum n =[ sigma ]=>n
| Lookup: forall v sigma , avar v =[ sigma ]=>(sigma v)
| Add : forall a1 a2 i1 i2 n sigma,
    a1 =[ sigma ]=>i1 ->
    a2 =[ sigma ]=>i2 ->
    n = i1 + i2 ->
    a1 +' a2 =[ sigma ]=>n
| Mul : forall a1 a2 i1 i2 n sigma,
    a1 =[ sigma ]=>i1 ->
    a2 =[ sigma ]=>i2 ->
    n  = i1 * i2 ->
    a1 *' a2 =[ sigma ]=>n
| Div : forall a1 a2 i1 i2 n sigma,    
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n  = Nat.div i1 i2 -> 
   a1 /' a2 =[ sigma ]=> n
| Mod : forall a1 a2 i1 i2 n sigma,
   a1 =[ sigma ]=> i1->
   a2 =[ sigma ]=> i2->
   n  = i1 mod i2 ->      
   a1 %' a2 =[ sigma ]=>n
| Sub : forall a1 a2 i1 i2 n sigma,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n  = i1 - i2 ->
    a1 -' a2 =[ sigma ]=> n
where "A =[ E ]=> N" := (aconfig A E N).
Print sigma1.
Example ex1: 2 +' "x"=[ sigma1 ]=> 12.
Proof.
  apply Add with (i1 :=2)(i2 := 10).
  -apply Const.
  -apply Lookup.
  -simpl. reflexivity. (*sau eauto*)
Qed.
(*5.5.2*)

Example ex2: ("x" +' 2) *' ("i" +' 3) =[ sigma1 ]=>36.
Proof.
  eapply Mul.
  -eapply Add.
    +apply Lookup.
    +apply Const.
    +simpl. reflexivity.
  -eapply Add.
    +apply Lookup.
    +apply Const.
    +simpl. reflexivity.
  -simpl. reflexivity.
Qed.

Definition sal (n1 n2: nat ) : bool:=
Nat.ltb n1 n2.
Compute sal 2 3.



