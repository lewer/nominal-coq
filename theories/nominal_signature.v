From Ssreflect
Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq fintype.
From MathComp
Require Import finfun finset generic_quotient bigop tuple.

Require Import finmap finsfun finperm nominal_multisorted utilitaires.

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

|Atom : forall (a : satom atom_sort), rterm (atom_arity a.1)
|C : forall (c : cons), rterm (cons_arity c) -> rterm (data_arity (cons_res c))
|Pair : forall a1 a2, rterm a1 -> rterm a2 -> rterm (pair_arity a1 a2)
|B : forall (a : satom atom_sort) ar, rterm ar -> rterm (binding_arity a.1 ar).

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

Fixpoint rterm_act (ar : arity) (s : atom_sort)
         (π : {finperm atom}) (t : rterm ar)  : rterm ar :=
  match t with
    |Atom a => Atom (π \dot_(s) a)
    |C c t => C c (rterm_act s π t)
    |Pair _ _ t1 t2 => Pair (rterm_act s π t1) (rterm_act s π t2)
    |B x _ t => B (π \dot_(s) x) (rterm_act s π t)
  end.

Fixpoint rterm_support (ar : arity) (s : atom_sort) (t : rterm ar) :=
  match t with
    |Atom a => support s a
    |C c t => rterm_support s t
    |Pair _ _ t1 t2 => rterm_support s t1 `|` rterm_support s t2
    |B x _ t => support s x `|` rterm_support s t 
  end.

Fixpoint rdepth (ar : arity) (t : rterm ar) :=
  match t with
    |Atom _ => 0
    |C _ t => (rdepth t).+1
    |Pair _ _ t1 t2 => (maxn (rdepth t1) (rdepth t2)).+1
    |B _ _ t => (rdepth t).+1
  end.

Context (ar : arity).

Lemma rterm_act1 s : @rterm_act ar s 1 =1 id.
Proof.
elim => /= [[s' a]|c t ->|ar1 ar2 t1 -> t2 ->|[s' a] art t ->] //.
all: by rewrite/act/=/satomact/= finsfun1 if_same. 
Qed.

Lemma rterm_actM s π π' (t : rterm ar) :
  rterm_act s (π * π') t = rterm_act s π (rterm_act s π' t).
Proof.
elim: t => /= [[s' a]|c t ->|ar1 ar2 t1 -> t2 ->|[s' a] art t ->]//.
all: by rewrite/act/=/satomact/= finsfunM; case: (s == s').
Qed. 

Lemma rterm_actproper s : forall t1 t2 π, t1 = t2 -> (@rterm_act ar s π t1) = (@rterm_act ar s π t2).
Proof. by move => t1 t2 π ->. Qed.

Definition rterm_nominal_setoid_mixin :=
  @PermSetoidMixin _ atom_sort (rterm ar) (@eq (rterm ar)) (@rterm_act ar) rterm_act1
                   rterm_actM rterm_actproper.

Lemma rterm_act_id s (π : {finperm atom}) (t : rterm ar) :
     pfixe π (rterm_support s t) -> rterm_act s π t = t.
Proof.
elim: t => /= [[s' a] 
              |c t HFix /HFix -> //
              |a1 a2 t1 HFixt1 t2 HFixt2 /pfixeU [/HFixt1 -> /HFixt2 -> ]
              |[s' a] art t HFixt] //=.
all: rewrite/act/=/satomact/=/support/=/satom_support; case: (s == s') => //=.
- by move/pfixe1 ->.
- by move => /pfixe1U [-> /HFixt ->].
- by move => /pfixeU [_ /HFixt ->].
Qed.

Definition rterm_nominal_mixin :=
  @NominalMixin _ atom_sort _ rterm_nominal_setoid_mixin _ (rterm_act_id).

Canonical rterm_nominalType :=
  NominalType atom atom_sort (rterm ar) rterm_nominal_mixin.

End NominalRterm.

Section AlphaEquivalence.

Fixpoint alpha_rec (n : nat) (ar1 ar2 : arity) (t1 : rterm ar1) (t2 : rterm ar2) :=
  match n, t1, t2 with
    |_, Atom a1, Atom a2 => a1 == a2
    |S m, C c1 u1, C c2 u2 => alpha_rec m u1 u2
    |S m, Pair _ _ u1  v1, Pair _ _ u2 v2 => alpha_rec m u1 u2 && alpha_rec m v1 v2
    |S m, B x1 _ t1, B x2 _ t2 =>
     (x1.1 == x2.1) &&
     let z := fresh_in x1.1 (x1, x2, t1) in
     alpha_rec m (swap x1.2 z \dot_(x1.1) t1) (swap x2.2 z \dot_(x2.1) t2)
    |_,_,_ => false
  end.

Definition alpha (ar1 ar2 : arity) (t1 : rterm ar1) (t2 : rterm ar2) := 
  alpha_rec (rdepth t1) t1 t2.

Lemma rdepth_perm (π : {finperm atom}) {ar} s (t : rterm ar) :
  rdepth (π \dot_(s) t) = rdepth t.
Proof.
elim: t => [[s' a]|c t IHt|art1 art2 t1 IHt1 t2 IHt2|[s' a] art t IHt] //=.
all: by rewrite ?IHt ?(IHt1, IHt2).
Qed.

Lemma alpha_recE n (ar1 ar2 : arity) (t1 : rterm ar1) (t2 : rterm ar2) :
  (rdepth t1 <= n) -> alpha_rec n t1 t2 = alpha t1 t2.
Proof.
rewrite /alpha; move: {-2}n (leqnn n).
elim: n ar1 ar2 t1 t2 => [|n IHn] ar1 ar2 [[s1 a1]|c1 t1|art1 art1' t1 t1'|[s1 a1] art1 t1]
                          [[s2 a2]|c2 t2|art2 art2' t2 t2'|[s2 a2] art2 t2] [|m] //=.
all: rewrite !ltnS. 
  - by move => /(IHn _ _ t1 t2) //.
  - rewrite geq_max => mn /andP [t1m t2m].
    by rewrite !IHn // ?(leq_maxl, leq_maxr) ?geq_max
            ?(leq_trans t1m, leq_trans t2m).
  - move => mn t1m. apply/andb_id2l => _.
    rewrite !IHn // ?rdepth_perm //; exact/(leq_trans t1m).
Qed.

End AlphaEquivalence.

End FixedSignature.

End ArityDef.