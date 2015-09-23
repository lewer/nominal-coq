From Ssreflect
Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq fintype.
From MathComp
Require Import finfun finset generic_quotient bigop tuple.

Require Import finmap finsfun finperm nominal utilitaires.

Require Import EqdepFacts.

Require Import Equations.Equations.

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
all: by rewrite ?IHt ?IHt1 ?IHt2.
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
    rewrite !IHn // ?leq_maxl ?leq_maxr ?geq_max //
            ?(leq_trans t1m) // ?(leq_trans t2m) //.
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
Proof. by rewrite/alpha/= !alpha_recE // ?leq_maxl ?leq_maxr. Qed.

Lemma alpha_rBE ar1 ar2 x1 x2 (t1 : rterm ar1) (t2 : rterm ar2) :
  alpha (rB x1 t1) (rB x2 t2) = 
  let z := fresh_in (x1, x2, t1, t2) in 
  alpha (swap x1 z \dot t1) (swap x2 z \dot t2).
Proof. by rewrite/alpha/= rdepth_perm. Qed.

Definition alphaE := (alpha_rAtomE, alpha_rCE, alpha_rPairE, alpha_rBE).

Lemma alpha_BP ar1 ar2 (x1 x2 : atom) (t1 : rterm ar1) (t2 : rterm ar2) :
  reflect (\new z, (alpha (swap x1 z \dot t1) (swap x2 z \dot t2)))
          (alpha (rB x1 t1) (rB x2 t2)).
Proof.
apply: (equivP idP). rewrite alpha_rBE /=.
set y := fresh_in _.
pose R := fun z (x : atom * atom * (rterm ar1) * (rterm ar2)) =>
                alpha (swap x.1.1.1 z \dot x.1.2) (swap x.1.1.2 z \dot x.2) = true.
apply/(@some_fresh_new _ R _ y (x1, x2, t1, t2)); last exact/fresh1P.
move => π z [[[a b] u1] u2]. 
by rewrite/R/= -act_conj -[X in alpha _ X]act_conj alpha_equivariant.
Qed.

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

Lemma alpha_trans ar1 ar2 ar3 (t2 : rterm ar2) (t1 : rterm ar1) (t3 : rterm ar3) :
  alpha t1 t2 -> alpha t2 t3 -> alpha t1 t3.
Proof.
move: {-1}(rdepth t1) (leqnn (rdepth t1)) => n.
elim: n ar1 ar2 ar3 t1 t2 t3 => [|n IHn] ar1 ar2 ar3
                                         [x2|c2 t2|? ? t2 t2'|? x2 t2]
                                         [x1|c1 t1|? ? t1 t1'|? x1 t1]
                                         [x3|c3 t3|? ? t3 t3'|? x3 t3] //.
  - rewrite !alpha_rAtomE => _. exact/eq_op_trans.
  - rewrite !alpha_rAtomE => _. exact/eq_op_trans.
  - rewrite /= ltnS => /(IHn _ _ _ t2 t1 t3) Htrans. 
    rewrite !alpha_rCE => /andP [c1_eq_c2 t1t2] /andP [c2_eq_c3 t2t3].
    apply/andP; split; first exact/(@eq_op_trans _ c1 c2 c3).
    exact/Htrans.
  - rewrite !alpha_rPairE /= ltnS geq_max => /andP [? ?] /andP [? ?] /andP [? ?].
    apply/andP; split; first exact/(@IHn _ _ _ t2 t1 t3) => //.
    exact/(@IHn _ _ _ t2' t1' t3').
  - rewrite /= ltnS => ? /alpha_BP [St1t2 Ht1t2] /alpha_BP [St2t3 Ht2t3].
    apply/alpha_BP. exists (St1t2 `|` St2t3) => a aF.
    apply/IHn; first by rewrite rdepth_perm.
      exact/Ht1t2/(fresh_fsetU1 aF).
    exact/Ht2t3/(fresh_fsetU2 aF).
Qed.
    
End AlphaEquivalence.

Section Quotient.

Context (s : arity).

Canonical alpha_equiv :=
  EquivRel (@alpha s s) (@alpha_refl s) (@alpha_sym s s) (@alpha_trans s s s).

Definition term := {eq_quot (@alpha s s)}.
Definition term_eqMixin := [eqMixin of term].
Canonical term_eqType := EqType term term_eqMixin.
Canonical term_choiceType := Eval hnf in [choiceType of term].
Canonical term_countType := Eval hnf in [countType of term].
Canonical term_quotType := Eval hnf in [quotType of term].
Canonical term_eqQuotType := Eval hnf in
      [eqQuotType (@alpha s s) of term].

Lemma alpha_eqE (t t' : rterm s) : alpha t t' = (t == t' %[mod term]).
Proof. by rewrite piE. Qed.

End Quotient.

Definition Atom x := lift_cst (term _) (rAtom x).

Lemma rAtomK x : \pi (rAtom x) = Atom x.
Proof. by unlock Atom. Qed.

Definition C c := lift_op1 (term _) (rC c).
Arguments C : clear implicits.

Lemma rCK c t : \pi (rC c t) = C c (\pi t).
Proof.
unlock C => /=. apply/eqP.
by rewrite [_ == _]piE alphaE eqxx /= alpha_eqE reprK. 
Qed.

Definition Pair ar1 ar2 := 
  lift_op2 (term _) (@rPair ar1 ar2).

Lemma rPairK ar1 ar2 (t1 : rterm ar1) (t2 : rterm ar2) :
  \pi (rPair t1 t2) = Pair (\pi t1) (\pi t2).
Proof.
unlock Pair => /=; apply /eqP.
by rewrite [_ == _]piE !alphaE !alpha_eqE !reprK !eqxx.
Qed.

Definition B ar x := lift_op1 (term _) (@rB ar x).
Lemma rBK ar x (t : rterm ar) : \pi (rB x t) = B x (\pi t). 
Proof.
unlock B; apply/eqP.
by rewrite [_ == _]piE alphaE /= alpha_equivariant alpha_eqE reprK. 
Qed.

Section NominalTerm.

Context (ar : arity).

Implicit Types (π : {finperm atom}).

Definition termact π (t : term ar) := \pi_(term ar) (π \dot repr t).

Lemma termact1 : termact 1 =1 id.
Proof. move => t /=. by rewrite /termact act1 reprK. Qed.

Lemma termact_equiv π t :
  π \dot (repr t) == repr (termact π t) %[mod (term ar)].
Proof. by rewrite /termact reprK. Qed.

Lemma termactM π π' t : termact (π * π') t = termact π (termact π' t).
Proof.
apply/eqP.
by rewrite /termact actM piE alpha_equivariant alpha_eqE reprK.
Qed.

Lemma termactproper :
  forall t1 t2 π, t1 = t2 -> (termact π t1) = (termact π t2).
Proof. by move => t1 t2 π ->. Qed.

Definition term_nominal_setoid_mixin :=
  @PermSetoidMixin _ (term ar) (@eq (term ar)) termact termact1 termactM termactproper.

Lemma termact_id π t :
     pfixe π (support (repr t)) -> termact π t = t.
Proof.
rewrite/termact => Hact_id.
by rewrite act_id // reprK.
Qed.

Definition term_nominal_mixin :=
  @NominalMixin _ _ term_nominal_setoid_mixin _ termact_id.

Canonical term_nominalType := NominalType atom (term ar) term_nominal_mixin.

End NominalTerm.

Section VariousLemmas.

Lemma pi_equivariant ar π (t : rterm ar) :
  π \dot (\pi_(term ar) t) = \pi (π \dot t).
Proof.
apply/eqmodP => /=.
by rewrite alpha_equivariant alpha_eqE reprK.
Qed.

Lemma repr_equivariant ar π (t : term ar) : repr (π \dot t) == π \dot (repr t) %[mod (term ar)].
Proof. by rewrite -pi_equivariant !reprK. Qed.

Lemma Atom_equivariant π x : π \dot (Atom x) = Atom (π x).
Proof. by rewrite -rAtomK pi_equivariant /= rAtomK. Qed.

Lemma C_equivariant π c (t : term (cons_arity c)) :
  π \dot (C c t) = C c (π \dot t).
Proof.
unlock C.
by rewrite pi_equivariant !rCK reprK -pi_equivariant reprK. 
Qed.

Lemma Pair_equivariant ar1 ar2 π (t1 : term ar1) (t2 : term ar2) :
  π \dot (Pair t1 t2) = Pair (π \dot t1) (π \dot t2).
Proof.
unlock Pair.
by rewrite pi_equivariant !rPairK -!pi_equivariant !reprK. 
Qed.

Lemma B_equivariant ar π x (t : term ar) :
  π \dot (B x t) = B (π x) (π \dot t).
Proof.
unlock B.
by rewrite pi_equivariant !rBK reprK -pi_equivariant reprK.
Qed.

Lemma fresh_repr x ar (t : term ar) : x # (repr t) -> x # t.
Proof.
move => [S [xNS S_supp_t]].
exists S; split => //.
move => π H. by rewrite -[t]reprK pi_equivariant (S_supp_t π) //.
Qed.

(* Lemma fresh_pi x t : x # t -> x # (\pi_W t). *)
(* Proof. *)
(* move => [S [xNS S_supp_t]]. *)
(* exists S; split => //. *)
(* move => π H. by rewrite pi_equivariant (S_supp_t π). *)
(* Qed. *)

(* Lemma eq_BConsE c x1 x2 a1 a2 f1 f2 : *)
(*   @BCons c x1 a1 f1 = @BCons c x2 a2 f2 -> *)
(*   a1 = a2 /\ *)
(*   forall z, z # (x1, x2, f1, f2) -> *)
(*              swap x1 z \dot f1 = swap x2 z \dot f2. *)
(* Proof. *)
(* unlock BCons => /eqP. *)
(* rewrite -alpha_eqE alpha_BConsE => /andP [/eqP ->] /=. *)
(* set z := fresh_in _ => /forallP Halpha. *)
(* split => // z'. *)
(* repeat(move/fresh_prod; case); move => *. *)
(* apply/(@act_inj _ _ (swap z z'))/funext => i. *)
(* freshTacCtxt z. *)
(* rewrite [LHS]act_conj [RHS]act_conj !tfinpermR !tfinperm_fresh //. *)
(* rewrite ![swap z z' \dot _]act_fresh. *)
(*   by move: (Halpha i); rewrite alpha_eqE -!pi_equivariant !reprK => /eqP. *)
(* 1: apply/fresh_repr; change (z # (repr \o f2) i). *)
(* 3: apply/fresh_repr; change (z # (repr \o f1) i). *)
(* all:exact/fresh_fun. *)
(* Qed. *)

Lemma AtomK x : repr (Atom x) = rAtom x.
Proof.
have : alpha (repr (Atom x)) (rAtom x).
  by rewrite alpha_eqE reprK rAtomK.
generalize (repr (Atom x)). 
depelim r.
by rewrite alphaE => /eqP ->.
Qed.

Require Import Equations.DepElimDec EqdepFacts.
Instance: EqDec.EqDec data_sort.
Admitted.
Instance: EqDec.EqDec cons.
Admitted.

Derive Signature for rterm.
Derive Signature for @eq.

Lemma alpha_transport a a' (r : rterm a) (r' : rterm a') (Heq : a = a') : 
  alpha (eq_rect _ _ r _ Heq) r' = alpha r r'.
by destruct Heq. 
Qed.


Lemma CK c t  : exists t', repr (C c t) = rC c t'.
Proof.
have: alpha (repr (C c t)) (rC c (repr t)).
  by rewrite alpha_eqE reprK rCK reprK.
generalize (repr (C c t)) as r.
intros r. revert t.
generalize_eqs_sig r.
induction r; try solve [ simplify_dep_elim ].
intros r0.
intros.
case: (eq_comparable c c0).
move => c_eq_c0. subst c0.
revert H.
simplify_dep_elim.
by exists r.
apply sym_eq, eq_sigT_sig_eq in H.
destruct H as [? eqr].
rewrite <- eqr in x.
rewrite alpha_transport in x.
move:x. rewrite alphaE => /andP [/eqP] c0_eq_c _ //. 
by rewrite c0_eq_c.
Qed.

Arguments CK : clear implicits.

Lemma PairK ar1 ar2 (t1 : term ar1) (t2 : term ar2) : 
  exists t1' t2', repr (Pair t1 t2) = rPair t1' t2'.
Admitted.


(* Lemma BConsK c x a f : exists (y : atom) f', *)
(*    repr (@BCons c x a f) = @rBCons c y a f'. *)
(* Proof. *)
(* have: alpha (repr (@BCons c x a f)) (@rBCons c x a (repr \o f)). *)
(*   by rewrite alpha_eqE reprK rBConsK pi_reprK. *)
(* case: (repr (BCons _ _ _)) => //= c2 x2 a2 f2. *)
(* have [/eqP c_eq_c2|/eqP c_neq_c2 /alpha_BCons_eqc] := boolP (c == c2); *)
(*     last by congruence. *)
(* subst. *)
(* move/alpha_BConsP => [a2_eq_a _]. *)
(* exists x2; exists f2. *)
(* by rewrite a2_eq_a. *)
(* Qed. *)


(* Lemma Var_inj : injective Var. *)
(* Proof. *)
(* move => x y /(congr1 repr). rewrite !VarK => H. by injection H. Qed. *)

(* Lemma Cons_inj c a1 a2 f1 f2 : *)
(*   @Cons c a1 f1 = @Cons c a2 f2 -> a1 = a2 /\ f1 = f2. *)
(* Proof. *)
(* move/(congr1 repr). *)
(* have [f1' [-> ->]] := @ConsK c a1 f1. *)
(* have [f2' [-> ->]] := @ConsK c a2 f2. *)
(* move => H; injection H. *)
(* move/eq_sigT_sig_eq => [p]. *)
(* have -> /= : p = erefl c by apply/eq_axiomK. *)
(* move => -> /eq_sigT_sig_eq => [[q]]. *)
(* have -> /= : q = erefl c by apply/eq_axiomK. *)
(* by []. *)
(* Qed. *)

(* Lemma BConsx_inj c x a1 a2 f1 f2 : *)
(*   (@BCons c x a1 f1 = @BCons c x a2 f2) -> a1 = a2 /\ f1 = f2. *)
(* Proof. *)
(* pose z := fresh_in (x, f1, f2). *)
(* move => /eq_BConsE [a1_eq_2] /(_ z) H. *)
(* split => //. *)
(* apply/(@act_inj _ _ (swap x z)). *)
(* freshTacCtxt z. *)
(* apply/H. by repeat (apply/fresh_prod; split). *)
(* Qed. *)

(* Lemma fresh_Var x y : x # (Var y) -> x # y. *)
(* Proof. *)
(* move => [S] [xNS S_supp_Ly]. *)
(* exists S; split => // π HS. *)
(* apply Var_inj. rewrite -Var_equivariant. *)
(* exact: S_supp_Ly. *)
(* Qed. *)

(* (* Lemma fresh_Cons x c a f : x # (@Cons c a f) -> x # a. *) *)
(* (* Proof. *) *)
(* (* move => [S] [xNS S_supp_caf]. *) *)
(* (* exists S; split => // π HS. *) *)
(* (* eapply proj2; apply Cons_inj. rewrite -Cons_equivariant. *) *)
(* (* exact: S_supp_cl. *) *)
(* (* Qed. *) *)

(* Lemma fresh_rBCons x y c a f : *)
(*   x # (@rBCons c y a f) -> x # (y, f). *)
(* Proof. *)
(* move => [S] [xNS S_supp_cyl]. *)
(* exists S; split => // π Hπ. *)
(* move: (S_supp_cyl π Hπ) => H.  injection H. *)
(* move => /eq_sigT_sig_eq [p]. *)
(* have -> /= : p = erefl c by apply eq_axiomK. *)
(* move => πf_eq_f. *)
(* by rewrite prodactE atomactE -{2}πf_eq_f => ->. *)
(* Qed. *)

(* Lemma fresh_BCons x y c a f : *)
(*   x # y -> x # (@BCons c y a f) -> x # f. *)
(* Proof. *)
(* move => [S] [xNS S_supp_y] [S'] [xNS' S'_supp_cyf]. *)
(* exists (S `|` S'); split. *)
(*   by rewrite in_fsetU negb_or xNS xNS'. *)
(* move => π Hπ. *)
(* apply/(proj2 (@BConsx_inj c y a a _ _ _)). *)
(* have y_eq_piy : π y = y. *)
(*   apply S_supp_y => b bS. apply Hπ. *)
(*   by rewrite in_fsetU bS. *)
(* rewrite -{1}y_eq_piy -BCons_equivariant. *)
(* apply S'_supp_cyf => b bS'. apply Hπ. *)
(* by rewrite in_fsetU bS' orbT. *)
(* Qed. *)

Lemma eq_B x y ar (t : term ar)  :
  y # (x, t) -> B x t = B y (swap x y \dot t).
Proof.
move/fresh_prod => [yFx yFt].
unlock B. apply/eqmodP.
rewrite /= alphaE /=. 
rewrite alpha_eqE -!pi_equivariant !reprK.
set z := fresh_in _. freshTacCtxt z.
rewrite act_conj tfinpermL tfinperm_fresh // [swap y z \dot t]act_fresh //. 
exact/fresh_repr.
Qed.

(* Lemma bname_fresh (x : atom) c a f : x # (@BCons c x a f). *)
(* Proof. *)
(* pose y := fresh_in (x, f, @BCons c x a f); freshTacCtxt y. *)
(* apply (@CFN_principle y) => //. *)
(* rewrite BCons_equivariant tfinpermL. *)
(* exact/sym_eq/eq_BCons/fresh_prod. *)
(* Qed. *)

End VariousLemmas.

Section Depth.

Definition depth ar (t : term ar) := rdepth (repr t).

Lemma rdepth_alpha (ar1 ar2 : arity) (t1 : rterm ar1) (t2 : rterm ar2) : 
  alpha t1 t2 -> rdepth t1 = rdepth t2.
Proof.
  elim: t1 ar2 t2 =>  [x1|c1 t1 IHt1|? ? t1 IHt1 t1' IHt1'|? x1 t1 IHt1] ar2
                             [x2|c2 t2|? ? t2 t2'|? x2 t2] //=.
  - by rewrite alphaE => /andP [_ /IHt1] ->. 
  - by rewrite alphaE => /andP [/IHt1 -> /IHt1' ->].
  - rewrite alphaE /=. set z := fresh_in _.
    rewrite -(alpha_equivariant _ _ (swap x1 z)) -actM tfinperm_idempotent act1 => /IHt1.
    by rewrite !rdepth_perm => ->.
Qed.

Lemma depth_rdepth ar (t : rterm ar) : depth (\pi t) = rdepth t.
Proof.
apply rdepth_alpha. by rewrite alpha_eqE reprK.
Qed.

Lemma rdepth_depth ar (t : term ar) : rdepth (repr t) = depth t.
Proof. by rewrite -depth_rdepth reprK. Qed.

Lemma depth_perm ar (t : term ar) π : depth (π \dot t) = depth t.
Proof.
rewrite/depth -[RHS](rdepth_perm π).
apply rdepth_alpha. rewrite alpha_eqE.
exact: repr_equivariant.
Qed.

Lemma depth_Atom x : depth (Atom x) = 0.
Proof. by rewrite/depth AtomK. Qed.

Lemma depth_C c t : depth (C c t) = (depth t).+1.
Proof. unlock C. by rewrite depth_rdepth /=. Qed.

Lemma depth_Pair ar1 ar2 (t1 : term ar1) (t2 : term ar2) :
  depth (Pair t1 t2) = (maxn (depth t1) (depth t2)).+1.
Proof.
unlock Pair. by rewrite depth_rdepth /= -!depth_rdepth !reprK.
Qed.

Lemma depth_BinderCons ar x (t : term ar) :
  depth (B x t) = (depth t).+1.
Proof. unlock B. by rewrite depth_rdepth. Qed.

End Depth.

Section EliminationPrinciples.

Lemma term_naive_ind (P : forall ar, (term ar) -> Prop) :
  (forall x, P _ (Atom x)) ->
  (forall c t, P _ t -> P _ (C c t)) ->
  (forall ar1 ar2 (t1 : term ar1) (t2 : term ar2), P _ t1 -> P _ t2 -> P _ (Pair t1 t2)) ->
  (forall ar x (t : term ar), P _ t -> P _ (B x t)) ->
  forall ar u, P ar u.
Proof.
move => HAtom HC HPair HB ar u; rewrite -[u]reprK.
elim: (repr u) => [x|c t|? ? t1 IHt1 t2 IHt2|? x t] /=.
  - by rewrite rAtomK.
  - rewrite rCK. exact/HC.
  - rewrite rPairK. exact/HPair.
  - rewrite rBK. exact/HB.
Qed.

Lemma term_ind {env : {nominalType atom}} (D : env) (P : forall ar, (term ar) -> Prop) :
  (forall x, P _ (Atom x)) ->
  (forall c t, P _ t -> P _ (C c t)) ->
  (forall ar1 ar2 (t1 : term ar1) (t2 : term ar2), P _ t1 -> P _ t2 -> P _ (Pair t1 t2)) ->
  (forall ar x (t : term ar), x # D -> P _ t -> P _ (B x t)) ->
  forall ar u, P ar u.
Proof.
move => HAtom HC HPair HB ar u.
suff : forall (π : {finperm atom}), P ar (π \dot u).
  by move => /(_ 1); rewrite act1.
elim/term_naive_ind : u => [x|c t IHt|? ? t1 IHt1 t2 IHt2|? x t IHt] π /=.
  - by rewrite Atom_equivariant.
  - rewrite C_equivariant. exact/HC. 
  - rewrite Pair_equivariant. exact/HPair.
  - rewrite B_equivariant.
    pose z := fresh_in (D, π \dot x, π \dot t); freshTacCtxt z.
    rewrite (@eq_B _ z _ _) -?actM; last exact/fresh_prod.
    exact/HB.
Qed.

Context (X : {nominalType atom})
        (f_atom : atom -> X)
        (f_C : forall (c : cons), term (cons_arity c) -> X -> X)
        (f_Pair : forall ar1 ar2, term ar1 -> term ar2 -> X -> X -> X)
        (f_B : forall ar, atom -> term ar -> X -> X)
        (Supp : {fset atom})
        (dflt : X).

Arguments f_C : clear implicits.

Hypothesis f_atom_equivariant :
  forall (π : {finperm atom}) x,
    [disjoint finsupp π & Supp] -> π \dot f_atom x = f_atom (π \dot x).

Hypothesis f_C_equivariant :
  forall (π : {finperm atom}) c t res_t,
    [disjoint finsupp π & Supp] ->
                  π \dot f_C c t res_t =
                  f_C c (π \dot t) (π \dot res_t).

Hypothesis f_Pair_equivariant :
  forall (π : {finperm atom}) ar1 ar2 (t1 : term ar1) (t2 : term ar2) res_t1 res_t2, 
    [disjoint finsupp π & Supp] -> 
    π \dot (f_Pair t1 t2 res_t1 res_t2) = 
    f_Pair (π \dot t1) (π \dot t2) (π \dot res_t1) (π \dot res_t2).

Hypothesis f_B_equivariant :
  forall (π : {finperm atom}) ar x (t : term ar) res_t,
    [disjoint finsupp π & Supp] -> π \dot f_B x t res_t =
                                   f_B (π x) (π \dot t) (π \dot res_t).

Hypothesis FCB :
  forall x ar (t : term ar) t', x # Supp -> x # (f_B x t t').

Fixpoint term_rect_rec (n : nat) ar (t : term ar) :=
  match n, (repr t) with
    |_, rAtom x => f_atom x
    |S n, rC c t => f_C c (\pi t) (term_rect_rec n (\pi t))
    |S n, rPair _ _ t1 t2 => f_Pair (\pi t1) (\pi t2) 
                                    (term_rect_rec n (\pi t1))
                                    (term_rect_rec n (\pi t2))
    |S n, rB _ x t => let z := fresh_in (Supp, rB x t) in
                      f_B z (swap x z \dot (\pi_(term _) t)) 
                          (term_rect_rec n (swap x z \dot \pi_(term _) t))
    |_,_ =>  dflt
  end.

Definition term_rect ar (t : term ar) := term_rect_rec (depth t) t.

Lemma term_rect_recE n ar (t : term ar) : 
  depth t <= n -> term_rect_rec n t = term_rect t.
Proof.
rewrite/term_rect; move: {-2}n (leqnn n).
elim: n ar t => [|n IHn] ar t //; rewrite /depth.
  by move => ?; repeat (rewrite leqn0 => /eqP ->).
move => [?|m]; first by rewrite leqn0 => /eqP ->.
set t' := (repr t); depelim t'.
  - subst t'. by rewrite /= H /= H.
  - subst t'0. rewrite /= H /= H !ltnS => m_leq_n t'_leq_m. 
    by rewrite IHn // depth_rdepth.
  - subst t'. rewrite /= H /= H !ltnS geq_max => m_leq_n /andP [t'1m t'2m].
    rewrite !IHn // ?depth_rdepth // ?leq_maxl ?leq_maxr // geq_max;
    apply/andP; split; exact/(leq_trans _ m_leq_n).
  - subst t'0; rewrite /= H /= H !ltnS => m_leq_n t'm.
    by rewrite IHn // ?pi_equivariant ?depth_rdepth ?rdepth_perm //.
Qed.

Lemma term_rect_AtomE x : term_rect (Atom x) = f_atom x.
Proof. by rewrite /term_rect depth_Atom /= AtomK. Qed.

Lemma term_rect_CE c t :
  term_rect (C c t) = f_C c t (term_rect t).
Proof.
rewrite/term_rect depth_C /= /=.
have [t'] := @CK c t.
congr f_cons => //.
apply/funext => i /=.
apply W_rect_recE => /=.
exact/leq_bigmax_cond.
Qed.



End FixedSignature.

End ArityDef.