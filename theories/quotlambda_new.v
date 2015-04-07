Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq.
Require Import bigop fintype finfun finset generic_quotient perm.
Require Import tuple.
Require Import fingroup.
Require Import finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition atom := nat.

Record finPerm := FinPerm {
  perm_of : {fmap atom -> atom};
  _ : injectiveb (perm_of)
}.

Definition support (p : finPerm) :=
  fset [seq a <- fset_keys (domf (perm_of p)) | fnd (perm_of p) a != Some a].

Definition fun_of_perm (p:finPerm) (a:atom) :=
  match fnd (perm_of p) a with
      |Some x => x
      |None => a
  end.

Coercion fun_of_perm : finPerm >-> Funclass.

