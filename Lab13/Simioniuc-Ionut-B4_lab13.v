
Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

(*Ex1*)
Inductive lambda : Type:=
 | Var : string -> lambda (*o variabila string ca identificator*)
 | Abs : string -> lambda -> lambda (*reprezinta o abstractie*)
 | App : lambda -> lambda -> lambda. (*reprezinta aplicatie*)

(*Ex2*)
Fixpoint Capturing_subst (M : lambda)(x : string)(N : lambda) : lambda :=
 match M with
 | Var y     => if string_dec x y then N else M
 | Abs y M1  => if string_dec x y then M else Abs y (Capturing_subst M1 x N)
 | App M1 M2 => App(Capturing_subst M1 x N)(Capturing_subst M2 x N)
 end.


Fixpoint alpha_convert (M : lambda) (x : string) (new_x : string) : lambda :=
  match M with
  | Var y => if string_dec x y then Var new_x else M
  | Abs y M1 => if string_dec x y then Abs y M1 else Abs y (alpha_convert M1 x new_x)
  | App M1 M2 => App (alpha_convert M1 x new_x) (alpha_convert M2 x new_x)
  end.

Fixpoint free_var (M : lambda) : list string :=
  match M with
  | Var x => [x]
  | Abs x M1 => free_var M1 (* Nu elimină `x` din listă *)
  | App M1 M2 => free_var M1 ++ free_var M2 (* Concatenează liste *)
  end.

Fixpoint subst (M : lambda) (x : string) (N : lambda) : lambda :=
  match M with
  | Var y => if string_dec x y then N else M
  | Abs y M1 => 
      if string_dec x y then Abs y M1 
      else Abs y (subst M1 x N)
  | App M1 M2 => App (subst M1 x N) (subst M2 x N)
  end.



Fixpoint Capturing_avoid_subst (M : lambda)(x : string)(N : lambda) : lambda :=
  match M with
  | Var y     => if string_dec x y then N else M
  | Abs y M1  => 
        if string_dec x y then 
            Abs y M1
        else 
            Abs y (Capturing_avoid_subst M1 x N)
  | App M1 M2 => App (Capturing_avoid_subst M1 x N) (Capturing_avoid_subst M2 x N)
  end.

(*Ex3*)

Definition beta_reduction (M : lambda) : lambda :=
  match M with
  | App (Abs x M1) N => subst M1 x N
  | _ => M (* Dacă M nu este o aplicație a unei abstracții, nu se face nicio reducere *)
  end.

(*Ex4*)
Fixpoint CBN (M : lambda) : lambda :=
  match M with
  | Var x => Var x
  | Abs x M1 => Abs x M1  (* Nu evaluăm corpul abstracției în CBN *)
  | App (Abs x M1) M2 => subst M1 x M2  (* Aplică β-reducerea direct *)
  | App M1 M2 => 
      match CBN M1 with  (* Evaluăm doar partea stângă a aplicației *)
      | Abs x M1' => subst M1' x M2
      | M1' => App M1' M2  (* Dacă M1' nu este o abstracție, returnăm aplicația *)
      end
  end.

(*Trebuiesc 2 exemple*)
(*exemplu 1: (λz.z) λx. ((λy.y)x) -> Beta*)

Definition example1 := App (Abs "z" (Var "z")) (Abs "x" (App (Abs "y" (Var "y")) (Var "x"))).

Eval compute in (CBN example1).
(*exemplu 2: (λx.(x x))((λz.z) λx.((λy.y)x))*)

Definition example2 := App 
                          (Abs "x" (App (Var "x") (Var "x")))
                          (App (Abs "z" (Var "z")) (Abs "x" (App (Abs "y" (Var "y")) (Var "x")))).

Eval compute in (CBN example2).


(*Ex5*)
Fixpoint CBV (M : lambda) : lambda :=
  match M with
  | Var x => Var x
  | Abs x M1 => Abs x M1  (* Nu evaluăm corpul abstracției în CBV *)
  | App M1 M2 =>
      let M1' := CBV M1 in
      let M2' := CBV M2 in
      match M1' with
      | Abs x M1_body => subst M1_body x M2'  (* Aplică β-reducerea cu argumentul evaluat *)
      | _ => App M1' M2'  (* Dacă M1' nu este o abstracție, returnăm aplicația *)
      end
  end.

(*Trebuiesc 2 exemple*)
 
(*exemplu 1: (λf.f)((λz.z)λx.((λy.y)x))->beta *)

Definition example1_CBV := App 
                           (Abs "f" (Var "f"))
                           (App (Abs "z" (Var "z")) (Abs "x" (App (Abs "y" (Var "y")) (Var "x")))).

Eval compute in (CBV example1_CBV).


(*exemplu 2: (λx.(x x))((λz.z)λx.((λy.y)x))->beta*)
Definition example2_CBV := App 
                           (Abs "x" (App (Var "x") (Var "x")))
                           (App (Abs "z" (Var "z")) (Abs "x" (App (Abs "y" (Var "y")) (Var "x")))).

Eval compute in (CBV example2_CBV).

(*ex 6*)
Fixpoint lambda_eq_dec (x y : lambda) : {x = y} + {x <> y}.
Proof.
  decide equality; apply string_dec.
Defined.


Fixpoint reduce_to_normal (M : lambda) (limit : nat) : lambda :=
  match limit with
  | 0 => M  (* Limită pentru a evita buclele infinite *)
  | S limit' =>
      let M' := beta_reduction M in
      if lambda_eq_dec M M' then M  (* Verifică dacă s-a ajuns la o formă normală *)
      else reduce_to_normal M' limit'
  end.

(*
Lemma reduce_to_normal_idempotent : forall M limit, 
    reduce_to_normal (reduce_to_normal M limit) limit = reduce_to_normal M limit.
Proof.
    intros M limit.
  induction limit as [| limit' IH].
  - (* cazul de bază: limit = 0 *)
    simpl. reflexivity.
  - (* pasul inductiv: limit = S limit' *)
    simpl.
    destruct (lambda_eq_dec M (beta_reduction M)) eqn:HeqM.
    + (* cazul în care M este deja în forma normală *)
       simpl. rewrite HeqM. reflexivity.
    + 
         apply beta_reduction. rewrite IH. reflexivity.
Admited.*)



Theorem confluence : forall M N O limit,
    reduce_to_normal M limit = N -> reduce_to_normal M limit = O ->
    exists P, reduce_to_normal N limit = P /\ reduce_to_normal O limit = P.
Proof.
   intros.
  exists N; split.
  - rewrite <- H.   
Abort.


