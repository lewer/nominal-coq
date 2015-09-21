From Ssreflect
Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq fintype.
From MathComp
Require Import finfun finset generic_quotient bigop tuple.

Require Import finmap finsfun finperm nominal utilitaires.

Require Import EqdepFacts.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope finperm_scope with fperm.
Local Open Scope finperm_scope.
Local Open Scope fset.
Local Open Scope quotient_scope.

Import Key.Exports.

Section ArityDef.

Context (data_sort : finType).

Inductive arity  := 
|atom_arity : arity
|data_arity : data_sort -> arity
|pair_arity : arity -> arity -> arity
|binding_arity : arity -> arity.

Section FixedSignature.

Context (cons : eqType) 
        (cons_arity : cons -> arity) 
        (cons_res : cons -> data_sort).


Section RtermDef.

Inductive rterm : arity -> Type :=

|rAtom : forall (a : atom), rterm atom_arity
|rC : forall (c : cons), rterm (cons_arity c) -> rterm (data_arity (cons_res c))
|rPair : forall a1 a2, rterm a1 -> rterm a2 -> rterm (pair_arity a1 a2)
|rB : forall (ar : arity), atom -> rterm ar -> rterm (binding_arity ar).

End RtermDef.

Arguments rC c _ : clear implicits.

(* TODO : encodage des rAST *)
Definition rterm_encode (ar : arity) : rterm ar -> GenTree.tree atom. Admitted.
Definition rterm_decode (ar : arity) : GenTree.tree atom -> rterm ar. Admitted.
Lemma rterm_codeK (ar : arity) : cancel (@rterm_encode ar) (rterm_decode ar). Admitted.

Definition rterm_eqMixin (ar : arity) := CanEqMixin (@rterm_codeK ar).
Canonical rterm_eqType (ar : arity) := EqType (rterm ar) (rterm_eqMixin ar).
Definition rterm_choiceMixin (ar: arity) := CanChoiceMixin (@rterm_codeK ar).
Canonical rterm_choiceType (ar : arity) := ChoiceType (rterm ar) (@rterm_choiceMixin ar).
Definition rterm_countMixin (ar : arity) := CanCountMixin (@rterm_codeK ar).
Canonical rterm_countType (ar : arity) := CountType (rterm ar) (@rterm_countMixin ar).

Section NominalRterm.

Fixpoint rterm_act (ar : arity) (π : {finperm atom}) (t : rterm ar)  : rterm ar :=
  match t with
    |rAtom a => rAtom (π a)
    |rC c t => rC c (rterm_act π t)
    |rPair _ _ t1 t2 => rPair (rterm_act π t1) (rterm_act π t2)
    |rB _ x t => rB (π x) (rterm_act π t)
  end.

Fixpoint rterm_support (ar : arity) (t : rterm ar) :=
  match t with
    |rAtom a => [fset a]
    |rC c t => rterm_support t
    |rPair _ _ t1 t2 => rterm_support t1 `|` rterm_support t2
    |rB _ x t => x |` rterm_support t 
  end.

Fixpoint rdepth (ar : arity) (t : rterm ar) :=
  match t with
    |rAtom _ => 0
    |rC _ t => (rdepth t).+1
    |rPair _ _ t1 t2 => (maxn (rdepth t1) (rdepth t2)).+1
    |rB _ _ t => (rdepth t).+1
  end.

Context (ar : arity).

Lemma rterm_act1 : @rterm_act ar 1 =1 id.
Proof.
elim => /= [a|c t ->|ar1 ar2 t1 -> t2 ->|art a t ->] //.
all: by rewrite finsfun1.
Qed.

Lemma rterm_actM π π' (t : rterm ar) :
  rterm_act (π * π') t = rterm_act π (rterm_act π' t).
Proof.
elim: t => /= [a|c t ->|ar1 ar2 t1 -> t2 ->|art x t ->]//.
all: by rewrite finsfunM.
Qed. 

Lemma rterm_actproper : forall t1 t2 π, t1 = t2 -> (@rterm_act ar π t1) = (@rterm_act ar π t2).
Proof. by move => t1 t2 π ->. Qed.

Definition rterm_nominal_setoid_mixin :=
  @PermSetoidMixin _ (rterm ar) (@eq (rterm ar)) (@rterm_act ar) rterm_act1
                   rterm_actM rterm_actproper.

Lemma rterm_act_id (π : {finperm atom}) (t : rterm ar) :
     pfixe π (rterm_support t) -> rterm_act π t = t.
Proof.
elim: t => /= [a 
              |c t HFix /HFix -> //
              |a1 a2 t1 HFixt1 t2 HFixt2 /pfixeU [/HFixt1 -> /HFixt2 -> ]
              |art a t HFixt] //=.
- by move/pfixe1 ->.
- by move => /pfixe1U [-> /HFixt ->].
Qed.

Definition rterm_nominal_mixin :=
  @NominalMixin _ _ rterm_nominal_setoid_mixin _ (rterm_act_id).

Canonical rterm_nominalType :=
  NominalType atom (rterm ar) rterm_nominal_mixin.

End NominalRterm.

Section AlphaEquivalence.

Fixpoint alpha_rec (n : nat) (ar1 ar2 : arity) (t1 : rterm ar1) (t2 : rterm ar2) :=
  match n, t1, t2 with
    |_, rAtom x1, rAtom x2 => x1 == x2
    |S m, rC c1 u1, rC c2 u2 => (c1 == c2) && (alpha_rec m u1 u2)
    |S m, rPair _ _ u1  v1, rPair _ _ u2 v2 => alpha_rec m u1 u2 && alpha_rec m v1 v2
    |S m, rB _ x1 t1, rB _ x2 t2 =>
     let z := fresh_in (x1, x2, t1, t2) in
     alpha_rec m (swap x1 z \dot t1) (swap x2 z \dot t2)
    |_,_,_ => false
  end.

Definition alpha (ar1 ar2 : arity) (t1 : rterm ar1) (t2 : rterm ar2) := 
  alpha_rec (rdepth t1) t1 t2.

Lemma rdepth_perm (π : {finperm atom}) {ar} (t : rterm ar) :
  rdepth (π \dot t) = rdepth t.
Proof.
elim: t => [a|c t IHt|art1 art2 t1 IHt1 t2 IHt2|art a t IHt] //=.
all: by rewrite ?IHt ?(IHt1, IHt2).
Qed.

Lemma alpha_recE n (ar1 ar2 : arity) (t1 : rterm ar1) (t2 : rterm ar2) :
  (rdepth t1 <= n) -> alpha_rec n t1 t2 = alpha t1 t2.
Proof.
rewrite /alpha; move: {-2}n (leqnn n).
elim: n ar1 ar2 t1 t2 => [|n IHn] ar1 ar2 [x1|c1 t1|art1 art1' t1 t1'|art1 x1 t1]
                          [x2|c2 t2|art2 art2' t2 t2'|art2 x2 t2] [|m] //=.
all: rewrite !ltnS. 
  - by move => /(IHn _ _ t1 t2) H /H ->.
  - rewrite geq_max => mn /andP [t1m t2m].
    by rewrite !IHn // ?(leq_maxl, leq_maxr) ?geq_max
            ?(leq_trans t1m, leq_trans t2m).
  - move => mn t1m. 
    rewrite !IHn // ?rdepth_perm //; exact/(leq_trans t1m).
Qed.

Lemma alpha_equivariant ar1 ar2 (t1 : rterm ar1) (t2 : rterm ar2) (π : {finperm atom}):
  alpha (π \dot t1) (π \dot t2) = alpha t1 t2.
Proof.
rewrite/alpha rdepth_perm.
move: {-1}(rdepth t1) (leqnn (rdepth t1)) => n.
elim: n ar1 ar2 t1 t2 π => [|n IHn] ar1 ar2
                                    [x1|c1 t1|art1 art1' t1 t1'|art1 x1 t1]
                                    [x2|c2 t2|art2 art2' t2 t2'|art2 x2 t2] π //=;
  do ?by rewrite inj_eq //; apply/finperm_inj.
all: rewrite ltnS.
  - by move/(IHn _ _ t1 t2 π) ->.
  - rewrite geq_max => /andP [t1n t1'n]; by rewrite !IHn //.
  - set z := fresh_in _; set y := fresh_in _.
    rewrite -act_conj_imL -[X in alpha_rec _ _ X]act_conj_imL => t1n.
    rewrite IHn ?rdepth_perm // -[RHS](IHn _ _ _ _ (swap y (π^-1 z))) ?rdepth_perm //.
    freshTacCtxt z. freshTacCtxt y.
    rewrite -{1}[t1 in LHS](@act_fresh _ y (π^-1 z)) //; last exact/im_inv_fresh.
    rewrite -{1}[t2 in LHS](@act_fresh _ y (π^-1 z)) //; last exact/im_inv_fresh.
    do ?rewrite [swap y _ \dot _  \dot _]act_conj tfinpermL tfinperm_fresh //;
      exact/im_inv_fresh.
Qed.

Lemma alpha_rAtomE (x y : atom) :
  alpha (rAtom x) (rAtom y) = (x == y).
Proof. by []. Qed.

Lemma alpha_rCE c1 c2 t1 t2 : 
  alpha (rC c1 t1) (rC c2 t2) = (c1 == c2) && (alpha t1 t2).
Proof. by []. Qed.

Lemma alpha_rPairE aru1 aru2 art1 art2 
      (u1 : rterm aru1) (u2 : rterm aru2) (t1 : rterm art1) (t2 : rterm art2) : 
  alpha (rPair t1 u1) (rPair t2 u2) = (alpha t1 t2) && (alpha u1 u2).
Proof. by rewrite/alpha/= !alpha_recE // ?(leq_maxl, leq_maxr). Qed.

Lemma alpha_rBE ar1 ar2 x1 x2 (t1 : rterm ar1) (t2 : rterm ar2) :
  alpha (rB x1 t1) (rB x2 t2) = 
  let z := fresh_in (x1, x2, t1, t2) in 
  alpha (swap x1 z \dot t1) (swap x2 z \dot t2).
Proof. by rewrite/alpha/= rdepth_perm. Qed.

Definition alphaE := (alpha_rAtomE, alpha_rCE, alpha_rPairE, alpha_rBE).

Lemma alpha_BConsP ar1 ar2 (x1 x2 : atom) (t1 : rterm ar1) (t2 : rterm ar2) :
  reflect (\new z, (alpha (swap x1 z \dot t1) (swap x2 z \dot t2)))
          (alpha (rB x1 t1) (rB x2 t2)).
Proof.
apply: (equivP idP). rewrite alpha_rBE /=.
set y := fresh_in _.
pose R := fun z (x : prod prodatom (prod atom (prod (rterm ar1) (rterm ar2 )))) => 
                alpha (swap x.1 z \dot x.2.2.1) (swap x.2.1 z \dot x.2.2.2) = true.
apply/(@some_fresh_new _ R _ y (x1, x2, t1, t2)); last first.
freshTac.
(* en cours *)

Lemma alpha_refl ar : reflexive (@alpha ar ar).
Proof.
elim => [x|c t IHt|ar1 ar2 t1 IHt1 t2 IHt2|ar' x t IH] /=;
rewrite ?alphaE //; try exact/andP.
by rewrite /= alpha_equivariant.
Qed.

Lemma alpha_sym ar1 ar2 (t1 : rterm ar1) (t2 : rterm ar2) :
                    alpha t1 t2 = alpha t2 t1.
Proof.
move: {-1}(rdepth t1) (leqnn (rdepth t1)) => n.
elim: n ar1 ar2 t1 t2 => /= [|n IHn] ? ? [x1|c1 t1 |ar1 ar1' t1 t1' |ar1 x1 t1]
                            [x2|c2 t2|ar2 ar2' t2 t2'|ar2 x2 t2] => //.
  - by rewrite !alpha_rAtomE eq_sym.
  - by rewrite !alpha_rAtomE eq_sym.
  - by move => ?; rewrite !alpha_rCE eq_sym IHn. 
  - rewrite /= ltnS geq_max => /andP [? ?]. 
    by rewrite !alpha_rPairE IHn // -[alpha t2' t1']IHn.
  - rewrite !alpha_rBE /= ltnS => ?. 
    rewrite IHn; last by rewrite rdepth_perm.
    rewrite/fresh_in; repeat(rewrite/support/=).
    by rewrite eq_fset2 -fsetUA [X in _ `|` X]fsetUC fsetUA.
Qed.

Lemma alpha_trans ar1 ar2 ar3 (t1 : rterm ar1) (t2 : rterm ar2) (t3 : rterm ar3) :
  alpha t1 t2 -> alpha t2 t3 -> alpha t1 t3.
Proof.
move: {-1}(rdepth t1) (leqnn (rdepth t1)) => n.
elim: n ar1 ar2 ar3 t1 t2 t3 => [|n IHn] ar1 ar2 ar3
                                         [x1|c1 t1|? ? t1 t1'|? x1 t1]
                                         [x2|c2 t2|? ? t2 t2'|? x2 t2]
                                         [x3|c3 t3|? ? t3 t3'|? x3 t3] //.
  - rewrite !alpha_rAtomE => _. exact/eq_op_trans.
  - rewrite !alpha_rAtomE => _. exact/eq_op_trans.
  - rewrite /= ltnS => /(IHn _ _ _ t1 t2 t3) Htrans. 
    rewrite !alpha_rCE => /andP [c1_eq_c2 t1t2] /andP [c2_eq_c3 t2t3].
    apply/andP; split; first exact/(@eq_op_trans _ c2 c1 c3).
    exact/Htrans.
  - rewrite !alpha_rPairE /= ltnS geq_max => /andP [? ?] /andP [? ?] /andP [? ?].
    apply/andP; split; first exact/(@IHn _ _ _ t1 t2 t3) => //.
    exact/(@IHn _ _ _ t1' t2' t3').
  - 

End AlphaEquivalence.

End FixedSignature.

End ArityDef.