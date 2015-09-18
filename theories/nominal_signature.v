From Ssreflect
Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq fintype.
From MathComp
Require Import finfun finset generic_quotient bigop tuple.

Require Import finmap finsfun finperm nominal utilitaires ilist.

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

Context (atom_sort data_sort : eqType).

Inductive arity  := 
|atom_arity : atom_sort -> arity
|data_arity : data_sort -> arity
|pair_arity : arity -> arity -> arity
|binding_arity : arity -> arity.

Section FixedSignature.

Context (cons : eqType) (cons_arity : cons -> arity) (cons_res : cons -> data_sort).

Section RtermDef.

Inductive rterm : arity -> Type :=
|Atom : forall (asort : atom_sort), atom -> rterm (atom_arity asort)
|C : forall (c : cons), rterm (cons_arity c) -> rterm (data_arity (cons_res c))
|Pair : forall a1 a2, rterm a1 -> rterm a2 -> rterm (pair_arity a1 a2)
|B : atom -> forall a, rterm a -> rterm (binding_arity a).

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

Fixpoint rterm_act (ar : arity) (π : {finperm atom}) (t : rterm ar)  : rterm ar :=
  match t with
    |Atom i x => Atom i (π x)
    |C c t => C c (rterm_act π t)
    |Pair _ _ t1 t2 => Pair (rterm_act π t1) (rterm_act π t2)
    |B x _ t => B (π x) (rterm_act π t)
  end.

Fixpoint rterm_support (ar : arity) (t : rterm ar) :=
  match t with
    |Atom _ x => [fset x]
    |C c t => rterm_support t
    |Pair _ _ t1 t2 => rterm_support t1 `|` rterm_support t2
    |B x _ t => x |` rterm_support t
  end.

Context (ar : arity).

Lemma rterm_act1 : @rterm_act ar 1 =1 id.
Proof.
elim => /= [i a|c t ->|ar1 ar2 t1 -> t2 ->|a art t ->] //; by rewrite finsfun1.
Qed.

Lemma rterm_actM π π' (t : rterm ar) :
  rterm_act (π * π') t = rterm_act π (rterm_act π' t).
Proof.
elim: t => /= [i a|c t ->|ar1 ar2 t1 -> t2 ->|a art t ->] //; by rewrite finsfunM.
Qed. 

Lemma rterm_actproper : forall t1 t2 π, t1 = t2 -> (@rterm_act ar π t1) = (@rterm_act ar π t2).
Proof. by move => t1 t2 π ->. Qed.

Definition rterm_nominal_setoid_mixin :=
  @PermSetoidMixin _ (rterm ar) (@eq (rterm ar)) (@rterm_act ar) rterm_act1
                   rterm_actM rterm_actproper.

Lemma rterm_act_id (π : {finperm atom}) (t : rterm ar) :
     pfixe π (rterm_support t) -> rterm_act π t = t.
Proof.
elim: t => /= [i a Hfix
              |c t HFix /HFix -> //
              |a1 a2 t1 HFixt1 t2 HFixt2 /pfixeU [fixet1 fixet2]
              |a art t HFixt /pfixe1U [-> fixet]] .
- by rewrite Hfix // in_fset1 eqxx.
- by rewrite HFixt1 // HFixt2.
- by rewrite HFixt.
Qed.

Definition rterm_nominal_mixin  :=
  @NominalMixin _ (@rterm_choiceType ar) rterm_nominal_setoid_mixin _
                rterm_act_id.

Canonical rterm_nominalType :=
  NominalType atom (rterm ar) rterm_nominal_mixin.

End NominalRterm.

End FixedSignature.

End ArityDef.