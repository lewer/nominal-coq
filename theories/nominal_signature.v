From Ssreflect
Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq fintype.
From MathComp
Require Import finfun finset generic_quotient bigop tuple.

Require Import finmap finsfun finperm nominal_multisorted utilitaires ilist.

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

Context (atom_sort data_sort : finType).

Inductive arity  := 
|atom_arity : atom_sort -> arity
|data_arity : data_sort -> arity
|pair_arity : arity -> arity -> arity
|binding_arity : atom_sort -> arity -> arity.

Section FixedSignature.

Context (cons : eqType) 
        (cons_arity : cons -> arity) 
        (cons_res : cons -> data_sort).


Section RtermDef.

Inductive rterm : arity -> Type :=
(* structure canonique atom_sort * atom marche pas ? *)
|Atom : forall (a :  atom_nominal_type atom_sort), rterm (atom_arity a.1)
|C : forall (c : cons), rterm (cons_arity c) -> rterm (data_arity (cons_res c))
|Pair : forall a1 a2, rterm a1 -> rterm a2 -> rterm (pair_arity a1 a2)
|B : forall (a : atom_nominal_type atom_sort) ar, rterm ar -> rterm (binding_arity a.1 ar).

End RtermDef.

Arguments C c _ : clear implicits.

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

Variables (x : atom_nominal_type atom_sort) (π : {finperm atom}) (aso : atom_sort).

Fixpoint rterm_act (ar : arity) (asort : atom_sort)
         (π : {finperm atom}) (t : rterm ar)  : rterm ar :=
  match t with
    |Atom x => Atom (π \dot_(asort) x)
    |C c t => C c (rterm_act asort π t)
    |Pair _ _ t1 t2 => Pair (rterm_act asort π t1) (rterm_act asort π t2)
    |B x _ t => B (π \dot_(asort) x) (rterm_act asort π t)
  end.

Fixpoint rterm_support (ar : arity) (asort : atom_sort) (t : rterm ar) :=
  match t with
    |Atom x => atom_support asort x
    |C c t => rterm_support asort t
    |Pair _ _ t1 t2 => rterm_support asort t1 `|` rterm_support asort t2
    |B x _ t => atom_support asort x `|` rterm_support asort t 
  end.

Fixpoint rdepth (ar : arity) (t : rterm ar) :=
  match t with
    |Atom _ _ => 0
    |C _ t => (rdepth t).+1
    |Pair _ _ t1 t2 => (maxn (rdepth t1) (rdepth t2)).+1
    |B _ _ _ t => (rdepth t).+1
  end.

Context (ar : arity).

Lemma rterm_act1 : @rterm_act ar 1 =1 id.
Proof.
by elim => /= [i a|c t ->|ar1 ar2 t1 -> t2 ->|aso a art t ->] //; 
rewrite finsfun1 if_same.
Qed.

Lemma rterm_actM π π' (t : rterm ar) :
  rterm_act (π * π') t = rterm_act π (rterm_act π' t).
Proof.
elim: t => /= [aso a|c t ->|ar1 ar2 t1 -> t2 ->|aso a art t ->] //.
all: rewrite finsfunM. 
all: by case: (aso == asort).
Qed. 

Lemma rterm_actproper : forall t1 t2 π, t1 = t2 -> (@rterm_act ar π t1) = (@rterm_act ar π t2).
Proof. by move => t1 t2 π ->. Qed.

Definition rterm_nominal_setoid_mixin :=
  @PermSetoidMixin _ (rterm ar) (@eq (rterm ar)) (@rterm_act ar) rterm_act1
                   rterm_actM rterm_actproper.

Lemma rterm_act_id (π : {finperm atom}) (t : rterm ar) :
     pfixe π (rterm_support t) -> rterm_act π t = t.
Proof.
elim: t => /= [aso a 
              |c t HFix /HFix -> //
              |a1 a2 t1 HFixt1 t2 HFixt2 /pfixeU [fixet1 fixet2]
              |aso a art t HFixt]. 
- by case: (aso == asort) => // /pfixe1 ->.
- by rewrite HFixt1 // HFixt2.
- case: (aso == asort); last by move=>/HFixt ->.
  by move/pfixe1U => [-> /HFixt ->].
Qed.

End NominalRterm.

Definition rterm_nominal_mixin (ar : arity) (aso : atom_sort) :=
  @NominalMixin _ (@rterm_choiceType ar) (rterm_nominal_setoid_mixin aso ar) _
                (@rterm_act_id aso ar).

Canonical rterm_nominalType (ar : arity) (aso : atom_sort) :=
  NominalType atom (rterm ar) rterm_nominal_mixin.

Notation "π \dot_( aso ) t" := (rterm_act aso π t) (at level 70).

Section AlphaEquivalence.

Variables (n : nat) (ar1 ar2 : arity) (t1 : rterm ar1) (t2 : rterm ar2) (aso : atom_sort).
Variable (π : {finperm atom}).

Fixpoint alpha_rec (n : nat) (ar1 ar2 : arity) (t1 : rterm ar1) (t2 : rterm ar2) :=
  match n, t1, t2 with
    |_, Atom i x, Atom j y => (i == j) && (x == y)
    |S m, C c1 u1, C c2 u2 => alpha_rec m u1 u2
    |S m, Pair _ _ u1  v1, Pair _ _ u2 v2 => alpha_rec m u1 u2 && alpha_rec m v1 v2
    |S m, B aso1 x1 _ t1, B aso2 x2 _ t2 => 
     (aso1 == aso2) &&
     let x3 := @fresh_in _ (x1, x2, t1) in
     alpha_rec m (swap x1 x3 \dot_(aso1) t1) (swap x2 x3 \dot_(aso2) t2)
    |_,_,_ => false
  end.

Definition alpha (ar1 ar2 : arity) (t1 : rterm ar1) (t2 : rterm ar2) := 
  alpha_rec (rdepth t1) t1 t2.

Lemma alpha_recE n (ar1 ar2 : arity) (t1 : rterm ar1) (t2 : rterm ar2) :
  (rdepth t1 <= n) -> alpha_rec n t1 t2 = alpha t1 t2.
Proof.
rewrite /alpha; move: {-2}n (leqnn n).
elim: n ar1 ar2 t1 t2 => // [|n IHn] ar1 ar2 [i1 a1|c1 t1|art1 art1' t1 t1'|x1 art1 t1]
                          [i2 a2|c2 t2|art2 art2' t2 t2'|x2 art2 t2] [|m] //=.
all: rewrite !ltnS. 
  - by move => /(IHn _ _ t1 t2) //.
  - rewrite geq_max => m_leq_n /andP [t1m t1'm].
    rewrite !IHn //.

End FixedSignature.

End ArityDef.