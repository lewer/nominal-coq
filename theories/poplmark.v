From Ssreflect
Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq fintype.
From MathComp
Require Import bigop  finfun finset generic_quotient perm tuple fingroup.

Require Import finmap finsfun finperm nominal nominal_signature.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope finperm_scope with fperm.
Local Open Scope finperm_scope.
Local Open Scope fset.
Local Open Scope quotient_scope.

Import Key.Exports.

Section Definitions.

Inductive data_sort := T.

Inductive cons := top | arrow | all.
Definition cons_nat (c : cons) :=
  match c with
    |top => 0
    |arrow => 1%nat
    |all => 2
  end.
Definition nat_cons (n : nat) :=
  match n with
    |0 => top
    |1 => arrow
    |_ => all
  end.
Lemma cons_natK : cancel cons_nat nat_cons.
Proof. by case. Qed.
Definition cons_eqMixin := CanEqMixin cons_natK.
Canonical cons_eqType := EqType cons cons_eqMixin.

Definition cons_arity (c : cons) :=
  match c with
    |top => unit_arity data_sort
    |arrow => pair_arity (data_arity T) (data_arity T)
    |all => pair_arity (binding_arity (data_arity T)) (data_arity T)
  end.

Definition cons_res (c : cons) := T.

Definition type := term cons_arity cons_res (data_arity T).
Definition Var (x : atom) := Atom cons_arity cons_res x.
Definition Top := @C _ _ cons_arity cons_res top (Unit cons_arity cons_res).
Definition Arrow t1 t2 := @C _ _ cons_arity cons_res arrow (Pair t1 t2).
Definition All x t1 t2 := @C _ _ cons_arity cons_res all (Pair (B x t1) t2).

Definition Var