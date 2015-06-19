From Ssreflect
Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq fintype.
From MathComp
Require Import bigop  finfun finset generic_quotient perm tuple fingroup.
From Nominal
Require Import finmap finsfun finperm nominal ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope finperm_scope with fperm.
Local Open Scope finperm_scope.
Local Open Scope fset.
Local Open Scope quotient_scope.

Import Key.Exports.

Inductive rawterm : Type :=
| rVar of atom
| rApp of rawterm & rawterm
| rLambda of atom & rawterm.

Inductive ulc_cons :=
|ulc_app| ulc_lam.

Definition rAST_ulc := rAST ulc_cons atom_nominal_type.
Definition rLeaf_ulc := @rLeaf ulc_cons atom_nominal_type.
Definition rCons_ulc := @rCons ulc_cons atom_nominal_type.
Definition rBinderCons_ulc := @rBinderCons ulc_cons atom_nominal_type.

Fixpoint ulc_encode (t : rawterm) : rAST_ulc :=
  match t with
    |rVar x => rLeaf_ulc x
    |rApp t1 t2 => rCons_ulc ulc_app [:: ulc_encode t1; ulc_encode t2]
    |rLambda x t => rBinderCons_ulc (ulc_lam, x) [:: ulc_encode t]
  end.

Fixpoint ulc_decode (W : rAST_ulc) : rawterm :=
  match W with
    |rLeaf x => rVar x
    |rCons ulc_app [:: W1; W2] => rApp (ulc_decode W1) (ulc_decode W2)
    |rBinderCons (ulc_lam, x) [:: Z] => rLambda x (ulc_decode Z)
    |_ => rVar 0
  end.

Lemma ulc_encodeK : cancel ulc_encode ulc_decode. 
Proof. by elim => //= [? -> ? ->|? ? ->]. Qed.

Canonical ULC_as_AST := ASTInstance ulc_encodeK.