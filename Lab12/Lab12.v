Require Import String.
Definition Env := string -> nat .
Inductive AExp : Type :=
| aNum : nat -> AExp
| aVar : string->AExp
| aPlus : AExp -> AExp -> AExp
| aMinus : AExp -> AExp -> AExp
| aMult : AExp -> AExp -> AExp.

Inductive Cond :=
| base : bool -> Cond
| bnot : Cond -> Cond
| beq  : AExp -> AExp -> Cond
| bless : AExp -> AExp -> Cond
| band : Cond -> Cond -> Cond.
Coercion base : bool >-> Cond.


Inductive Stmt :=
| skip : Stmt 
| assign : string -> AExp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt (* if-then-else *)
| it  : Cond -> Stmt -> Stmt (* if-then *)
| dowhile : Stmt -> Cond -> Stmt.

Notation "A ::= B" := (assign A B) (at level 97, right associativity).
Notation "S1 ;; S2" := (seq S1 S2) (at level 98, right associativity).

Fixpoint aeval (a : AExp) (e : Env) : option nat :=
  match a with
  | aNum v     => (Some v)
  | aVar x     => (Some (e x))
  | aPlus a1 a2 => match aeval a1 e with 
                 | Some a1' => match aeval a2 e with
                               | Some a2' => Some(a1'+a2')
                               | None => None
                               end
                 | None => None
                 end
  | aMinus a1 a2 => match aeval a1 e with
                 | None     => None
                 | Some a1' => match aeval a2 e with
                              | None     => None
                              | Some a2' => if (Nat.ltb a1' a2')
                                            then None
                                            else Some (a1' - a2')
                              end
                 end 
 | aMult a1 a2 => match aeval a1 e with
                | None   => None
                | Some 0 => Some 0
                | Some a1' => match aeval a2 e with
                              | None     => None
                              | Some 0   => Some 0
                              | Some a2' => Some (Nat.mul a1' a2')
                              end
                 end  
end.


Inductive method_def : Type :=
| Method : string -> list (string * AExp) -> AExp -> method_def.

Inductive class_def : Type :=
| Class : string -> option string -> list (string * AExp) -> list method_def -> class_def.

Inductive car : Type :=
  | mkCar : string -> nat -> car.

Definition newCar (brand : string) (price : nat) : car :=
  mkCar brand price.

Definition getBrand (c : car) : string :=
  match c with
  | mkCar brand _ => brand
  end.

Definition getPrice (c : car) : nat :=
  match c with
  | mkCar _ price => price
  end.

Inductive Vehicle: Type :=
  | CarType : car->Vehicle.

Definition get_vehicle_info (v : Vehicle) : string :=
 match v with
 | CarType c => getBrand c 
end.

Definition myNewCar := newCar "Dacia" 10000.
Eval compute in(get_vehicle_info myNewCar).

(*Exemple de using*)
Definition my_car := newCar "Toyota" 10000.
Definition my_vehicle:= car my_car.

Definition main : string :=
  "A " ++ getBrand myNewCar ++ " costs " ++ (getPrice myNewCar) ++ ".".

Eval compute in main.

Definition Point_class : class_def :=
  Class "Point" None [( aVar "x"); ( aVar "y")]  
    [Method "setPoint" [("newX", ANum 0); ("newY", ANum 0)] (APlus (ANum 0) (ANum 0)); 
     Method "getX" [] (ANum 0);  
     Method "getY" [] (ANum 0)].  

Definition Circle_class : class_def :=
  Class "Circle" (Some "Point")
    [("radius", ANum 0)] 
    [Method "setCircle" [("newCenter", ANum 0); ("newRadius", ANum 0)] (APlus (ANum 0) (ANum 0)); 
     Method "getRadius" [] (ANum 0)].
Definition execute_method (m: method_def) : aexp :=
  match m with
  | Method _ _ body => body
  end.

Eval compute in execute_method (Method "getX" [] (ANum 42)).



