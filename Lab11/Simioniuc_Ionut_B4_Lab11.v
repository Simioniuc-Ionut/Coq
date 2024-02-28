Require Import String.
Require Import List.
Import ListNotations.

Inductive B :=
| T : B
| F : B
| neg : B -> B
| and : B -> B -> B
| or  : B -> B -> B.

(*-------EX1-------*)

Fixpoint interpret (b : B) : bool :=
 match b with
| T => true
| F => false
| neg b1 => negb (interpret b1)
| and b1 b2 => andb (interpret b1) (interpret b2)
| or b1 b2 => orb (interpret b1) (interpret b2)
end.

(*-----EX2-------*)
(*Stack Machine*)
Inductive Instruction :=
| push : nat -> Instruction
| inv : Instruction
| add : Instruction
| mul : Instruction.

Print Instruction.
Fixpoint run_instruction (i : Instruction) (stack : list nat) : list nat :=
  match i with
  | push n => match n with
              | O    => O :: stack
              | S n' => (S O) :: stack
              end
  | inv  => match stack with
             | (O   :: stack) => (S O) :: stack
             | (S O :: stack) => O :: stack
             | _   => stack 
            end 
  | add  => match stack with  
                | (O :: n1 :: stack')   => match n1 with 
                                          | O => O :: stack'
                                          | (S n1') => (S O) :: stack'
                                          end
                | (S O :: n2 :: stack') => match n2 with
                                          | O => (S O) :: stack'
                                          | (S n2') => (S O) :: stack'
                                          end
                | _ => stack
            end 
 | mul  => match stack with  
                | (O :: n1 :: stack')   => O  :: stack'
                | (S O :: n2 :: stack') => n2 :: stack'
                | _ => stack    
        end 
  end.

Compute run_instruction 
    inv 
    [1].
Compute run_instruction
     add
     [1;1].

(*-------EX3------*)
Fixpoint run_instructions
         (stpgm : list Instruction)
         (stack : list nat) :=
  match stpgm with
| []       => stack
| i :: is' => run_instructions
              is'
              (run_instruction i stack)
end.
Compute run_instructions
        [
         inv; 
         inv;
         inv; 
         add
        ]
        [0;1;0;0;1].
(*--------EX4--------*)
(*Compiler*)

Print B.
Print Instruction.
Fixpoint compile (b : B) : list Instruction :=
  match b with
 | T         => [push (S O)]
 | F         => [push O ]
 | neg b1    => (compile b1) ++
                [inv]
 | and b1 b2 => (compile b2) ++
                (compile b1) ++
                [mul]
 | or b1 b2  => (compile b2) ++
                (compile b1) ++
                [add]
 end. 

Compute compile
        (and ( neg T ) (F)).

Compute run_instructions
        (compile
        (neg T)).

(*------EX5------*)
Definition to_nat (b : bool) : nat :=
  match b with
  | true => 1 
  | false => 0
  end.

Lemma soundness_helper:
  forall b instrs stack,
    run_instructions ((compile b) ++ instrs) stack =
    run_instructions instrs (to_nat(interpret b) :: stack).
Proof.
  induction b; intros instrs stack ; trivial.
  -simpl. 
  SearchPattern ((_++_)%list=_).
  rewrite <- app_assoc.
  simpl.
  rewrite IHb.
  destruct (interpret b).
  +simpl. reflexivity.
  +simpl. reflexivity.
  -simpl.
   SearchPattern ((_++_)%list=_).
   rewrite <-app_assoc.
   rewrite IHb2.
  rewrite <-app_assoc.
  rewrite IHb1.
  simpl.
  destruct (interpret b1). 
  +simpl. reflexivity.
  +simpl. reflexivity.
  -simpl.
   rewrite <-app_assoc.
   rewrite IHb2.
   rewrite <-app_assoc.
   simpl.
  destruct (interpret b1); destruct (interpret b2) ; simpl ;trivial; rewrite IHb1; simpl; reflexivity.
Qed.

Theorem soundness :
  forall b,
    run_instructions (compile b) nil =  [to_nat (interpret b)].
Proof.
 intros b.
 rewrite <-app_nil_r with(l := (compile b)).
 apply soundness_helper.
Qed.



