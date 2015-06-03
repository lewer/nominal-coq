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

Section SubstDef.

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

Lemma FCB_f3 : FCB_supp fset0 subst_f3.
Proof. move => a u rec_u _. rewrite /subst_f3. exact: bname_fresh. Qed.


Definition subst := term_altrect subst_f1 subst_f2 subst_f3 (x |` support t) fset0 fset0 dflt.

Lemma subst_VarE y : subst (Var y) = if x == y then t else Var y. 
Proof.
by rewrite/subst term_altrect_VarE /subst_f1.
Qed.

Lemma subst_AppE t1 t2 : subst (App t1 t2) = App (subst t1) (subst t2).
Proof.
by rewrite/subst term_altrect_AppE /subst_f2.
Qed.

Lemma subst_LamE y u : y # (x, t) -> subst (Lambda y u) = Lambda y (subst u).
Proof.
move => yFxt.
apply term_altrect_LamE.
  exact: support_subst_f1.
  exact: support_subst_f2.
  exact: support_subst_f3.
  exact: FCB_f3. admit.
Admitted.

End SubstDef.

Notation " t { x := u } " := (subst x u t) (at level 0).

Lemma forget x u t : x # u -> u{x:=t} = u.
Proof.

(* induction sur u, en précisant que dans le cas Lambda y v, *)
(* on veut y # (x, t) *) 

elim/(@term_altind _ (x, t)): u => [y |t1 t2 IHt1 IHt2|y v yFxt IHt].
  - move/fresh_varP => /negPf x_neq_y. by rewrite subst_VarE x_neq_y.
  - move/fresh_app => [xFt1 xFt2]. 
    rewrite subst_AppE. by rewrite IHt1 // IHt2 //.
  - have xFy : x # y by admit.
    move/fresh_lam /(_ xFy) => H. by rewrite subst_LamE // IHt.
Admitted.

Lemma fresh_fact y z N L : z # (N,L) -> z # (N{y:=L}).
Proof.
elim/(@term_altind _ (z,y,L)) : N.
  - move => x.
    have [y_eq_x | /negPf y_neq_x] := boolP (y == x).
      by rewrite subst_VarE y_eq_x => /fresh_prod [? ?]. 
    by rewrite subst_VarE y_neq_x => /fresh_prod [? ?].
  - move => t1 t2 IHt1 IHt2 /fresh_prod [/fresh_app [zFt1 zFt2]] zFL.
    rewrite subst_AppE. apply/fresh_app. split.
      apply IHt1. admit.
    apply IHt2. admit.
  - move => x t xFzyL IHt /fresh_prod [/fresh_lam].
    rewrite subst_LamE => *; last by admit.
    pose a := fresh_in (Lambda x t{y:=L}, x).
    apply/(@CFN_principle _ a); first by admit.
    rewrite Lam_equiv fresh_transp.
Admitted.

Lemma substitution_lemma x y L M N : 
  x # (y, L) -> M{x:=N}{y:=L} = M{y:=L}{x:=N{y:=L}}.
Proof.
move /fresh_prod. move => [/fresh_atomP /negPf x_neq_y xFL]. 
elim/(@term_altind _ (x,y,N,L)) : M.
  - move => z. 
    have [x_eq_z|/negPf x_neq_z] := boolP (x == z).  
      rewrite !subst_VarE x_eq_z -{1}(eqP x_eq_z) eq_sym x_neq_y. 
      by rewrite subst_VarE x_eq_z.
      
    have [y_eq_z|/negPf y_neq_z] := boolP (y == z).
      rewrite !subst_VarE x_neq_z y_eq_z. 
      rewrite !subst_VarE y_eq_z. 
      by rewrite forget //.

    rewrite !subst_VarE x_neq_z y_neq_z.
    by rewrite !subst_VarE y_neq_z x_neq_z.

  - move => t1 t2 IHt1 IHt2.
    by rewrite !subst_AppE IHt1 IHt2.

  - move => a t aFxyNL IHt.
    rewrite !subst_LamE.
      by rewrite IHt.
    apply fresh_prod. split; first by admit.
    apply fresh_fact.
Admitted.