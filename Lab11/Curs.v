Require Import String.
Require Import List.
Import ListNotations.

Open Scope string_scope.


(*Expresions langage *)
Inductive Exp :=
| num : nat -> Exp
| var : string->Exp
| plus : Exp->Exp->Exp
| times: Exp->Exp->Exp.

Definition Env := string->nat.

Definition env0 : Env := fun x=> 0.

Fixpoint interpret
          (e : Exp)
          (sigma : Env) : nat :=
  match e with
  | num n => n
  | var x => sigma x
  | plus e1 e2 =>(interpret e1 sigma) + (interpret e2 sigma)
  | times e1 e2=>(interpret e1 sigma) * (interpret e2 sigma)
end.

Compute interpret 
        (times (plus (num 2) (var "x"))
            (num 10))
        env0.

(*Stack machine*)

Inductive Instr :=
| push_const : nat ->Instr
| push_var : string->Instr
| add : Instr
| mul : Instr.

Fixpoint run_instr
        (i : Instr)
        (stack : list nat)
         (sigma : Env) : list nat :=
    match i with
   | push_const n => n::stack (*pun n in varful stivei*) 
   | push_var x => (sigma x)::stack
   | add =>match stack with 
           | (n1 :: n2 ::stack' ) =>(n1+n2)::stack'
           | _ =>stack (*las stiva goala,daca am o sing val sau 0 in stiva*)
           end
    | mul =>match stack with 
           | (n1 :: n2 ::stack' ) =>(n1*n2)::stack'
           | _ =>stack (*las stiva goala,daca am o sing val sau 0 in stiva*)
           end
    end.

Compute run_instr
        add
        [1;2;4]
        env0.
Compute (push_const 10).
Compute run_instr 
          (push_const 10)
           nil
            env0.


(*nu vreau sa execut doar o instr,vreau o lista de instructiuni :->*)

Fixpoint run_instrs
          (instrs : list Instr)
          (stack : list nat)
          (sigma : Env): list nat :=
    match instrs with
   |[] => stack
   | i::is' => run_instrs
        is'      
      (run_instr i stack sigma) (*run instr executa o singura instructiune*)
       sigma
  end.

Compute run_instrs
      [push_const 2;
       push_var "x";
       add;
       push_const 10;
       mul;
       push_const 3;
       mul
       ]
      []
      env0.

(*Compiler*)

Fixpoint compile (e : Exp) : list Instr  :=
    match e with
  | num n =>[push_const n]
  | var x =>[push_var x]
  | plus e1 e2 =>
     (compile e2) ++ (* ++ -> concatenare de liste*)
     (compile e1) ++ 
     [add]
  | times e1 e2 =>
     (compile e2) ++
     (compile e1) ++ 
     [mul]
end.

Compute compile
  (times (plus (num 2) (var "x")) (num 10)).

Compute run_instrs
  (compile
  (times (plus (num 2) (var "x"))
            (num 10)))
  []
  env0.

(*Soundness*)

Lemma soundnes_helper :
    forall e sigma stack instrs,
      run_instrs(compile e ++ instrs) stack sigma = 
      run_instrs instrs(interpret e sigma :: stack) sigma. (*ce s ar intampla la fiecare pas ?*)
                                            (*acesta este o generalizare a ce am eu jos,asta e invariantul*)
Proof.
  induction e; intros;trivial.
  -simpl.
   SearchPattern ((_++_)%list=_). (*ma intereseaza app_assoc*)
   rewrite <-app_assoc.
  rewrite IHe2.
  rewrite <-app_assoc.
  apply IHe1.
 -simpl.
   SearchPattern ((_++_)%list=_). (*ma intereseaza app_assoc*)
   rewrite <-app_assoc.
  rewrite IHe2.
  rewrite <-app_assoc.
  apply IHe1.
Qed.
(*Am demonstrat un invariant*)


(*Trebuie sa aratam corectitudinea compilatorului*)
Theorem soundnees :
    forall e sigma ,
      run_instrs(compile e) [] sigma = 
        [interpret e sigma] . (*nu putem demonstra direct , am nevoie de un invariant*)
Proof.
  intros e sigma.
  rewrite <- app_nil_r with (l:= (compile e)).
  SearchPattern ((_++_)%list = _).
  rewrite soundnes_helper.
  simpl. reflexivity.
Qed.


(*Ce era invariant ? = ca sa justidic ca programul e corect :
  I catam o prop care era mereu adev in bucle.
bucle -> pot avea multimi infinite ,si am nevoie de o specificatie care sa arate ca propr e adv mereu
Programarea dinamica : Exprim sol problemei in sol a subproblemelor.
keywords  
! derecursivare .
! memorizare .

cand am bulce -> am nevoie de un invariant care ajuta la demonstr buclelor
invariantul -> nu o putem genera, trebuie sa o gastei uitandu te la program si sa ti dai seama
ce este mereu adevart!. 
*)

(*

Am facut un stack masina
UN compilator , interpetor

daca rulez instr in umra compilari intr o stiva vida si orice sigma -> o stiva un obt in varful ei rezultatul compilarii.
=> stiu ca orice as compila in cazul expresii => imi garanteaza ca rezultatul este acelasi.

!!Compilare certificata!!
Sigur compilatorul este corect
*)

(*
definim libaj
interpetor
stack machine complet
? compilator ? 
cum se definesc 


de dem propro
to_nat(ia un bool) -> si l trnasforma in nat
*)


