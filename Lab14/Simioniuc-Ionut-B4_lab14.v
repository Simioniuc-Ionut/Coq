
Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.
(*ex 1*)
(*definirea simbolurilor functionale cu aritatea lor*)
Inductive func_symbol : Type :=
  | FSymbol : string -> nat -> func_symbol.

(*definirea variabilelor*)
Inductive var : Type :=
  | Var : string -> var.

(*definirea F-termenilor*)
Inductive f_term : Type :=
  | VarTerm : var -> f_term
  | FuncTerm : func_symbol -> list f_term -> f_term.

(*exemple de simboluri functionale*)
Definition f1 := FSymbol "f1" 2.
Definition f2 := FSymbol "f2" 1.

(*2 exemple de F-termeni*)
Definition term1 := FuncTerm f1 [VarTerm (Var "x"); VarTerm (Var "y")].
Definition term2 := FuncTerm f2 [term1].
(*ex2*)
(*definirea tipului de substitutie ca o lista de perechi (variabila, termen)*)
Definition substitution := list (var * f_term).
(*functia de cautare in substitutie*)
Fixpoint lookup_subst (v : var) (sigma : substitution) : option f_term :=
  match sigma with
  | [] => None
  | (Var v0, t) :: sigma' =>
      match v with
      | Var v' => if string_dec v0 v' then Some t else lookup_subst v sigma'
      end
  end.

(*functia de substitutie*)
Fixpoint subst (t : f_term) (sigma : substitution) : f_term :=
  match t with
  | VarTerm v => match lookup_subst v sigma with
                 | Some t' => t'
                 | None => t
                 end
  | FuncTerm f args => FuncTerm f (map (fun arg => subst arg sigma) args)
  end.

(*exemplu de substitutie*)
Definition sigma_example : substitution := [(Var "x", VarTerm (Var "y")); (Var "z", term1)].

(*aplicarea substitutiei la un termen*)
Definition term_subst_example := subst term2 sigma_example.
