Require Import String.
Open Scope string_scope.


(*-------ex1--------*)
Definition Env := string -> nat .
Definition update (x : string )(val : nat )(env : Env): Env :=
  fun var => if(string_dec x var)
              then val
              else (env x).
Inductive AExp :=
| num : nat -> AExp
| var : string -> AExp
| add : AExp -> AExp -> AExp
| sub : AExp -> AExp -> AExp
| div : AExp -> AExp -> AExp.

Coercion num : nat >-> AExp.
Coercion var : string >-> AExp.


Notation "A +' B" := (add A B)(at level 50, left associativity).
Notation "A -' B" := (sub A B)(at level 50, left associativity).
Notation "A /' B"  := (div A B)(at level 40, left associativity).


Fixpoint aeval (a : AExp) (e : Env) : option nat :=
  match a with
  | num v     => (Some v)
  | var x     => (Some (e x))
  | add a1 a2 => match aeval a1 e with 
                 | Some a1' => match aeval a2 e with
                               | Some a2' => Some(a1'+a2')
                               | None => None
                               end
                 | None => None
                 end
  | sub a1 a2 => match aeval a1 e with
                 | None     => None
                 | Some a1' => match aeval a2 e with
                              | None     => None
                              | Some a2' => if (Nat.ltb a1' a2')
                                            then None
                                            else Some (a1' - a2')
                              end
                 end 
 | div a1 a2 => match aeval a1 e with
                | None   => None
                | Some 0 => Some 0
                | Some a1' => match aeval a2 e with
                              | None     => None
                              | Some 0   => None
                              | Some a2' => Some (Nat.div a1' a2')
                              end
                 end  
end.

Check option.
Check option nat.
Print option.
Check (Some 2).
Check None.

(*---------ex2--------*)
Inductive Cond :=
| base : bool -> Cond
| bnot : Cond -> Cond
| beq  : AExp -> AExp -> Cond
| bless : AExp -> AExp -> Cond
| band : Cond -> Cond -> Cond.
Coercion base : bool >-> Cond.

Check (bnot true).

Notation "A <' B" := (bless A B)
                      (at level 41, left associativity).
Notation "A =' B" := (beq A B)
                      (at level 44, left associativity).
Notation "A &' B" := (band A B)
                       (at level 50 , left associativity).
Notation "! A " := (bnot A)
                       (at level 49 , left associativity).
Notation "X1 !=' X2" := (!(X1 =' X2))(at level 61).
Notation "A |' B" := (bnot(band (bnot A) (bnot B)))
                       (at level 51 , left associativity).
Notation "A >' B" := (bnot(bless A B))
                       (at level 41 , left associativity).

Notation "A <=' B" := ((bless A B) |' (beq A B))
                       (at level 41 , left associativity).
Notation "A >=' B" := ((bnot(bless A B)) |' (beq A B))
                       (at level 41 , left associativity).

Notation "A +' B" := (add A B)
                       (at level 50, left associativity).
Notation "A -' B" := (sub A B)
                       (at level 50 , left associativity).
Notation "A /' B" := (div A B)
                       (at level 40, left associativity).
Check (add (num 2) (add (var "x") (div (num 2) (var "y")))).
Check (add  2) (add "x" (div 2 "y")).



Inductive Stmt :=
| skip : Stmt 
| assign : string -> AExp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt (* if-then-else *)
| while : Cond -> Stmt -> Stmt
| it   : Cond -> Stmt->Stmt.
Check (assign "x" ("x" +' 1)).

Notation "A ::= B" := (assign A B) (at level 97, right associativity).
Notation "S1 ;; S2" := (seq S1 S2) (at level 98, right associativity).



Compute negb true.
Check Nat.ltb.


Fixpoint beval (b : Cond) (e : Env) : option bool :=
  match b with 
  | base true  => Some (true)
  | base false => Some (false)
  | bnot cond1  => match beval cond1 e with
                  | None => None
                  | Some cond1' => Some (negb cond1')
                  end
  | band b1 b2 => match beval b1 e with
                  |None => None
                  |Some b1' =>match beval b2 e with
                              |None => None
                              |Some b2' => Some (andb b1' b2')
                              end
                  end
  | beq exp1 exp2 => match aeval exp1 e with
                    | None => None
                    | Some exp1' => match aeval exp2 e with
                                    |None => None
                                    |Some exp2' =>Some (Nat.eqb exp1' exp2')
                                    end
                    end
  | bless exp1 exp2 => match aeval exp1 e with
                     | None => None
                     | Some exp1'=>match aeval exp2 e with
                                    |None => None
                                    |Some exp2' =>Some (Nat.ltb exp1' exp2')
                                    end
                    end
end.

Fixpoint eval 
        (s : Stmt)
        (e : Env)
        (fuel : nat) 
        : Env :=
 match fuel with
| 0 => e
| S fuel1 => match s with
            |skip => e
            |assign s1 exp1 => match aeval exp1 e with
                               |None => e 
                               |Some val => update s1 val e
                               end
            |ite cond1 s1 s2=> match beval cond1 e with
                              |None         => e (*daca e None at nu se executa nici o ramura a if ului*)
                              |Some (true)  => eval s1 e fuel
                              |Some (false) => eval s2 e fuel
                              end
            |it cond1 s1 => match beval cond1 e with
                                 | None => e(*daca conditia returneaza None, atunci nu se va executa niciuna dintre ramurile if-ului *)
                                 | Some (true) => eval s1 e fuel
                                 | Some (false) => e
                                 end            
            |seq s1 s2      => eval s2 (eval s1 e fuel) fuel
            |while cond1 s1 => match beval cond1 e with
                               |None => e (*daca e None at nu se executa while*)
                               |Some(true)  => eval s1 e fuel
                               |Some(false) => e
                               end
             end
end.

Definition empty_env := fun _:string => 0.


Definition Euclid (a b : string):=
  
  it(a=' 0)
    ("result" ::= b);;
  it(a='0 &' (b!=' 0))
    ("result" ::= a);;
  it((a!='0) &' (b!='0))
  (
  it(a!='b)
    (   while ( a !=' b) (
        ite(a>'b)(a ::= a -' b)(b::=b-'a)
    )
    );;
  "result" ::= a 
 ).
   
Definition env : string->nat :=
  fun x => if eqb x "n" then 10 else 0.

Compute (eval (Euclid "a" "b")(update "b" 2 (update "a" 4 env)) 100)"result".

Definition Fibbo(m:string) :=
      "a'" ::= 0 ;;
      "b'" ::= 1 ;;
      "nr" ::= 1 ;;
      ite(m =' 1)("response" ::= 0)(
        while("nr"<'m)(
          "b'" ::="b'" +' "a'";;
          "a'" ::="b'" -' "a'";;
          "nr" ::="nr" +' 1
          );;      
        "response" ::= "a'"  
      ).

Compute (eval (Fibbo "m")(update "m" 10 env) 100) "response".

(*------ex3------*)
(* Definirea sintaxei logicii propoziționale *)
Inductive prop :=
  | Var : nat -> prop
  | Not : prop -> prop
  | And : prop -> prop -> prop
  | Or : prop -> prop -> prop
  | Implies : prop -> prop -> prop.




