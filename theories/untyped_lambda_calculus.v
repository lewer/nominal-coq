From mathcomp
Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq fintype.
From mathcomp
Require Import bigop  finfun finset generic_quotient perm tuple fingroup.

Require Import finmap finsfun finperm nominal w.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope finperm_scope with fperm.
Local Open Scope finperm_scope.
Local Open Scope fset.
Local Open Scope quotient_scope.

Import Key.Exports.

Section Definitions.

Inductive cons_label := app.
Inductive bcons_label := lam.

Definition cons_label_I0 x := match x with |app => 0 end.
Definition I0_cons_label (n : nat) := match n with |_ => app end.
Lemma cons_label_I0K : cancel cons_label_I0 I0_cons_label.
Proof. by case. Qed.

Definition cons_label_EqMixin := CanEqMixin cons_label_I0K.
Canonical cons_label_eqType := Eval hnf in EqType cons_label cons_label_EqMixin.

Definition bcons_label_I0 x := match x with |lam => 0 end.
Definition I0_bcons_label (n : nat) := match n with |_ => lam end.
Lemma bcons_label_I0K : cancel bcons_label_I0 I0_bcons_label.
Proof. by case. Qed.

Definition bcons_label_EqMixin := CanEqMixin bcons_label_I0K.
Canonical bcons_label_eqType := Eval hnf in EqType bcons_label bcons_label_EqMixin.

Definition cons_annot c := match c with |app => unit_eqType end.
Definition cons_arity c := match c with |app => 2 end.
Definition bcons_annot c := match c with |lam => unit_eqType end. 
Definition bcons_arity c := match c with |lam => 1%nat end.

Definition term := W cons_annot cons_arity bcons_annot bcons_arity.

Definition Var := Var cons_annot cons_arity bcons_annot bcons_arity : atom -> term.

Definition one_to_I1 (t : term) (i : 'I_1) := t.
Definition I1_to_one (f : 'I_1 -> term) := f (inord 0).

Lemma one_to_I1K : cancel I1_to_one one_to_I1.
Proof.
move => f.
rewrite /one_to_I1/I1_to_one.
apply/funext => i. case: i. case => // i. 
congr f.
case: (inord 0); move => [|m] // i0.
congr Ordinal. exact/bool_irrelevance.
Qed.

Definition two_to_I2 (t1 t2 : term) (i : 'I_2) : term :=
  match (i : nat) with
    |0 => t1
    |1%nat => t2
    |_ => t1
  end.

Lemma two_to_I2K f : two_to_I2 (f (inord 0))  (f (inord 1)) = f.
Proof.
rewrite/two_to_I2.
apply/funext => i /=.
case_eq (i : nat).
  move => i0. congr f. apply ord_inj. 
  by rewrite i0 inordK. 
case.
  move => i1. congr f. apply ord_inj.
  by rewrite i1 inordK.
move => n in2. 
have H := (leq_ord i). by rewrite in2 in H. 
Qed.

Lemma two_to_I2_comp (t1 t2 : term) f : 
  f \o (two_to_I2 t1 t2) = two_to_I2 (f t1) (f t2).
Proof.
apply/funext => i /=.
rewrite/two_to_I2.
destruct (nat_of_ord i) => //.
by destruct n.
Qed.

(* comment on définit une fonction 'I_n -> X ? *)

Definition App t1 t2 := @Cons cons_label_eqType bcons_label_eqType 
                        cons_annot cons_arity bcons_annot bcons_arity app tt
                        (two_to_I2 t1 t2).

Definition Lam x t := @BCons cons_label_eqType bcons_label_eqType
                             cons_annot cons_arity bcons_annot bcons_arity lam x tt
                             (one_to_I1 t).

Lemma term_ind {env : nominalType atom} (C : env) (P : term -> Prop) :
  (forall x, P (Var x)) ->
  (forall t1 t2, P t1 -> P t2 -> P (App t1 t2)) ->
  (forall x t, x # C -> P t -> P (Lam x t)) ->
  forall u, P u.
Proof.
rewrite/App/Lam => HVar HApp HLam u.
apply/(@W_ind _ _ _ _ _ _ env C P) => [|[][] f Hf|[] x [] f xFC Hf].
  - exact/HVar.
  - rewrite -[f]two_to_I2K. exact/HApp/Hf.
  - rewrite -[f]one_to_I1K. apply/HLam => //.
    exact/Hf.
Qed.

Definition term_subst x (t : term) (u : term) := wsubst x t u : term. 

Notation " t { x := u } " := (term_subst x u t) (at level 0).

Lemma subst_varE x y u : (Var y){x := u} = if x == y then u else (Var y).
Proof. exact/wsubst_VarE. Qed.

Lemma subst_appE t1 t2 x u : 
  (App t1 t2){x := u} = App t1{x:=u} t2{x:=u}.
Proof.
by rewrite/App/term_subst wsubst_ConsE two_to_I2_comp.
Qed.

Lemma subst_lamE x y t u :
  y # x -> y # u -> (Lam y t){x := u} = Lam y (t{x := u}).
Proof.
move => yFx yFt.
by rewrite/Lam/term_subst wsubst_BConsE.
Qed.

Lemma forget x u t : x # u -> u{x := t} = u.
Proof.

(* induction sur u, en précisant que dans le cas Lambda y v, *)
(* on veut y # (x, t) *) 

elim/(@term_ind _ (x, t)): u => [y |t1 t2 IHt1 IHt2|y v yFxt IHt].
  - by rewrite subst_varE => /fresh_Var/fresh_atomP/negPf ->. 
  - move/fresh_app => [xFt1 xFt2]. 
    rewrite subst_AppE. by rewrite IHt1 // IHt2 //.
  - have xFy : x # y. by admit.
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