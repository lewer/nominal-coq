From Ssreflect
Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq fintype.

From MathComp
Require Import bigop  finfun finset generic_quotient perm tuple fingroup.
Require Import finmap finsfun finperm nominal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope finperm_scope with fperm.
Local Open Scope finperm_scope.
Local Open Scope fset.
Local Open Scope quotient_scope.

Section Subst.


Variables (x : atom) (t : term).

Definition dflt := Var 0.

Definition subst_f1 y := if x == y then t else Var y.
Definition subst_f2 (t1 t2 : term) subst_t1 subst_t2 :=
  App subst_t1 subst_t2.
Definition subst_f3 x (t : term) subst_t := Lambda x subst_t.

Lemma if_equivariant (X : nominalType) (b : bool) (t1 t2 : X) π :
  (π \dot (if b then t1 else t2)) = (if b then (π \dot t1) else (π \dot t2)). 
Proof. by case: b. Qed.

Lemma support_subst_f1 : function_support1 subst_f1 (x |` support t).
Proof.
move=>π; rewrite fset1_disjoint => /andP [xNπ disj_t_π] y.
have xNπinv : x \notin finsupp π^-1 by [].
by rewrite/subst_f1 if_equivariant Var_equiv atomactE [_ == π _]eq_sym 
finperm_can2eq eq_sym (finsfun_dflt xNπinv) (fresh_perm disj_t_π).
Qed.

Lemma support_subst_f2 : function_support4 subst_f2 fset0.
Proof.
move => π _ t1 t2 u1 u2. 
by rewrite /subst_f2 App_equiv.
Qed.

Lemma support_subst_f3 : function_support3 subst_f3 fset0.
Proof.
move => π _ y u v.
by rewrite /subst_f3 Lam_equiv.
Qed.

Lemma FCB_f3 : FCB subst_f3.
Proof.
exists (@fset0 nat_KeyType) => y u v.
admit.
Admitted.

Definition subst := term_altrect subst_f1 subst_f2 subst_f3 (x |` support t) fset0 fset0 dflt.

Lemma subst_VarE y : subst (Var y) = if x == y then t else Var y. 
Proof.
by rewrite/subst term_altrect_VarE /subst_f1.
Qed.

Lemma subst_AppE t1 t2 : subst (App t1 t2) = App (subst t1) (subst t2).
Proof.
by rewrite/subst term_altrect_AppE /subst_f2.
Qed.

Lemma subst_LamE y u : subst (Lambda y u) = Lambda y (subst u).
Proof.
rewrite/subst term_altrect_LamE /subst_f3 //.
  exact: support_subst_f1.
  exact: support_subst_f2.
  exact: support_subst_f3.
