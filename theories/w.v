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

Section W.

Context (cons_label : eqType)
        (bcons_label : eqType)
        (cons_annot : cons_label -> eqType)
        (cons_arity : cons_label -> nat)
        (bcons_annot : bcons_label -> eqType)
        (bcons_arity : bcons_label -> nat).

Section WDef.

Inductive rW := 
|rVar of atom
|rCons : forall (c : cons_label), 
           cons_annot c -> ('I_(cons_arity c) -> rW) -> rW
|rBCons : forall (c : bcons_label) (x : atom),
            bcons_annot c -> ('I_(bcons_arity c) -> rW) -> rW.

(* TODO : encodage des rAST *)
Definition rW_encode : rW -> GenTree.tree atom. Admitted.
Definition rW_decode : GenTree.tree atom -> rW. Admitted.
Lemma rW_codeK : cancel rW_encode rW_decode. Admitted.

Definition rW_eqMixin := CanEqMixin rW_codeK.
Canonical rW_eqType := EqType rW rW_eqMixin.
Definition rW_choiceMixin := CanChoiceMixin rW_codeK.
Canonical rW_choiceType := ChoiceType rW rW_choiceMixin.
Definition rW_countMixin := CanCountMixin rW_codeK.
Canonical rW_countType := CountType rW rW_countMixin.

Fixpoint rW_depth (t : rW) : nat :=
  match t with
    |rVar _ => 0
    |rCons c _ f => (\max_(i < cons_arity c) rW_depth (f i)).+1
    |rBCons c _ _ f => (\max_(i < bcons_arity c) rW_depth (f i)).+1
  end.

Fixpoint rW_act (π : {finperm atom}) (t : rW) :=
  match t with
    |rVar x => rVar (π x)
    |rCons c a f => @rCons c a (fun i => rW_act π (f i))
    |rBCons c x a f => @rBCons c (π x) a (fun i => rW_act π (f i))
  end.

Lemma rW_act1 : rW_act (1 atom) =1 id.
Proof. 
elim => [x|c a f IH|c x a f IH] /=.
  - by rewrite finsfun1.
  - congr rCons.
    exact/funext/IH.
  - rewrite finsfun1. congr rBCons.
    exact/funext/IH.
Qed.

Lemma rW_actM π π' (t : rW) : 
  rW_act (π * π') t = rW_act π (rW_act π' t).
Proof.
elim : t => [x|c a f IH|c x a f IH] /=.
  - by rewrite finsfunM.
  - congr rCons.
    exact/funext/IH.
  - rewrite finsfunM. congr rBCons.
    exact/funext/IH.
Qed.

Lemma rW_actproper : forall t1 t2 π, t1 = t2 -> (rW_act π t1) = (rW_act π t2).
Proof. by move => t1 t2 π ->. Qed.

Definition rW_nominal_setoid_mixin := 
  @PermSetoidMixin rW (@eq rW) atom rW_act rW_act1 
                   rW_actM rW_actproper.   


Fixpoint rW_support t :=
  match t with
    |rVar x => [fset x]
    |rCons c a f => \fbigcup_ (i in 'I_(cons_arity c)) (rW_support (f i))
    |rBCons c x a f => x |` 
                       \fbigcup_(i in 'I_(bcons_arity c)) (rW_support (f i))
  end.

Lemma fbigcupP {n} (F : 'I_n -> {fset atom}) x :
  reflect (exists i, x \in F i) (x \in \fbigcup_(i in 'I_n) (F i)).
Proof.
Admitted.

Lemma rW_act_id (π : {finperm atom}) (t : rW) :
     (forall a : atom, a \in rW_support t -> π a = a) -> rW_act π t = t.
Proof.
elim : t => [x|c a f IH|c x a f IH] Hsupp /=.
  - by rewrite Hsupp // in_fset1.
  - congr rCons.
    apply/funext => i. apply/IH => x x_supp_fi.
    apply/Hsupp/fbigcupP. by exists i.
  - rewrite Hsupp; last exact/fset1U1.
    congr rBCons.
    apply/funext => i. apply/IH => y y_supp_fi.
    apply/Hsupp/fsetUP; right. 
    apply/fbigcupP. by exists i.
Qed.

End WDef.

Definition rW_nominal_mixin  :=
  @NominalMixin rW_choiceType  atom rW_nominal_setoid_mixin _ 
                rW_act_id.

Canonical rW_nominalType := 
  @NominalType atom rW_choiceType rW_nominal_mixin.

Section rDepth.
  
Lemma rdepth_perm (π : {finperm atom}) (t : rW) : 
rW_depth (π \dot t) = rW_depth t.
Proof. 
elim : t => [x|c a f IH|c x a f IH] //;
exact/eq_S/eq_big.
Qed.

End rDepth.

Section AlphaEquivalence.

Fixpoint alpha_rec (n : nat) (W1 W2 : rW ) :=
  match n, W1, W2 with
    |_, rVar x, rVar y => x == y
    |S n, rCons c1 a1 f1, rCons c2 a2 f2 => 
     match (eq_comparable c1 c2) with
       |left p => (eq_rect c1 
                  (fun c => forall (a2 : cons_annot c) 
                                   (f2 : 'I_(cons_arity c) -> rW), bool) 
                  (fun a2 f2 => 
                     (a1 == a2) && 
                     [forall i in 'I_(cons_arity c1), alpha_rec n (f1 i) (f2 i)]) c2 p)
                    a2 f2
       |right _ => false
     end
    |S n, rBCons c1 x1 a1 f1, rBCons c2 x2 a2 f2 =>
     match (eq_comparable c1 c2) with
       |left p => 
        (eq_rect c1
                 (fun c => 
                    forall 
                      (x2 : atom)
                      (a2 : bcons_annot c)
                      (f2 : 'I_(bcons_arity c) -> rW), bool)
                 (fun x2 a2 f2 =>
                    (a1 == a2) && 
                     let m := bcons_arity c1 in
                     let z := fresh_in (x1, x2, f1, f2) in
                     [forall i in 'I_m, alpha_rec n (swap x1 z \dot f1 i)
                                                    (swap x2 z \dot f2 i)]) c2 p)
          x2 a2 f2                            
       |right _ => false
     end
    |_, _,_ => false
  end.

Definition alpha W1 W2 := alpha_rec (rW_depth W1) W1 W2.     

Lemma alpha_recE n (W1 W2 : rW) : 
  (rW_depth W1 <= n) -> 
  alpha_rec n W1 W2 = alpha W1 W2.
Proof.
rewrite /alpha; move: {-2}n (leqnn n). 
elim: n W1 W2 => // [|n ihn] [x1|c1 a1 f1|c1 x1 a1 f1] [x2|c2 a2 f2|c2 x2 a2 f2] [|m] //.
all: rewrite ltnS => m_leq_n IHf1 /=. 
all: case: (eq_comparable c1 c2) => // p. 
all: destruct p => /=; apply andb_id2l => _. 
all: apply eq_forallb => i. 
all: rewrite !ihn // ?rdepth_perm; 
  first exact/(@leq_trans m); first exact/leq_bigmax.
all: move: IHf1 => /bigmax_leqP /(_ i); exact.
Qed.

Lemma alpha_equivariant (W1 W2 : rW ) (π : {finperm atom}):
  alpha (π \dot W1) (π \dot W2) = alpha W1 W2.
Proof.
rewrite/alpha rdepth_perm.
move: {-1}(rW_depth W1) (leqnn (rW_depth W1)) => n.
elim: n W1 W2 π => [|n IHn] [x1|c1 a1 f1|c1 x1 a1 f1] 
                            [x2|c2 a2 f2|c2 x2 a2 f2] π //=;
  try solve [rewrite inj_eq //; exact: act_inj].
all: rewrite ltnS => /bigmax_leqP IHl1.
all: case: (eq_comparable c1 c2) => p //; destruct p => /=.
all: apply andb_id2l => _. 
all: apply eq_forallb => i.
  exact/IHn/IHl1.
set z := fresh_in _; set y := fresh_in _.
rewrite -act_conj_imL -[X in alpha_rec _ _ X]act_conj_imL.
rewrite IHn; try rewrite -[RHS](@IHn _ _ (swap y (π^-1 z)));
  try solve [rewrite rdepth_perm; exact: IHl1]. 
freshTacCtxt z; freshTacCtxt y.
rewrite -{1}[f1 i](@act_fresh _ y (π^-1 z)) //; 
  [|exact/fresh_fun|exact/fresh_fun/im_inv_fresh]. 
rewrite -{1}[f2 i](@act_fresh _ y (π^-1 z)) //; 
  [|exact/fresh_fun|exact/fresh_fun/im_inv_fresh]. 
rewrite 2?[in RHS]act_conj tfinpermL !tfinperm_fresh //.
all: exact/im_inv_fresh. 
Qed.

Lemma alpha_equivariantprop : equivariant_prop alpha.
Proof. move => π t t' /=. by rewrite alpha_equivariant. Qed.

Lemma alpha_VarP (x y : atom) :
  reflect (x = y) (alpha (rVar x) (rVar y)).
Proof. exact/eqP. Qed.

Lemma alpha_Cons_eqc (c1 c2 : cons_label) a1 a2 f1 f2 :
  alpha (@rCons c1 a1 f1) (@rCons c2 a2 f2) -> c1 = c2.
Proof. rewrite/alpha/=; by case: (eq_comparable c1 c2). Qed.

Lemma alpha_ConsP (c : cons_label) (a1 a2 : cons_annot c) f1 f2 :
  reflect (a1 = a2 /\ forall i, alpha (f1 i) (f2 i)) 
          (alpha (@rCons c a1 f1) (@rCons c a2 f2)).
Proof.
rewrite/alpha /=.
case: (eq_comparable c c) => p //.
have -> /= : p = erefl c by apply eq_axiomK.
(* comment prouver reflect sans iffP idP ? *)
apply: (iffP idP).
  move/andP => [/eqP -> /forallP] H.
  split => // i; move: (H i) => /=.
  rewrite alpha_recE //.
  exact/(@leq_bigmax _ (fun i => rW_depth (f1 i))). (* comment éviter ça ? *)
move => [->] H; rewrite eqxx /=.
apply/forallP => i /=.
rewrite alpha_recE; first exact/H.
exact/(@leq_bigmax _ (fun i => rW_depth (f1 i))). 
Qed.

Lemma alpha_BCons_eqc (c1 c2 : bcons_label) x1 x2 a1 a2 f1 f2 :
  alpha (@rBCons c1 x1 a1 f1) (@rBCons c2 x2 a2 f2) -> c1 = c2.
Proof. rewrite/alpha/=; by case: (eq_comparable c1 c2). Qed.

Lemma alpha_BConsE (c : bcons_label) (x1 x2 : atom) a1 a2 f1 f2 :
  alpha (@rBCons c x1 a1 f1) (@rBCons c x2 a2 f2) = 
  (a1 == a2) && let z := fresh_in (x1, x2, f1, f2) in
                [forall i, alpha (swap x1 z \dot (f1 i)) (swap x2 z \dot (f2 i))].
Proof.
rewrite/alpha/=.
case: (eq_comparable c c) => p //.
have -> /= : p = erefl c by apply eq_axiomK.
apply/andb_id2l => _.
apply/eq_forallb => i.
rewrite alpha_recE // rdepth_perm.
exact/(@leq_bigmax _ (fun i => rW_depth (f1 i))). 
Qed.

Lemma alpha_BConsP (c : bcons_label) (x1 x2 : atom) a1 a2 f1 f2  :
  reflect (a1 = a2 /\ 
           let n := bcons_arity c in
           \new z, (forall i, alpha (swap x1 z \dot (f1 i)) (swap x2 z \dot (f2 i))))
          (alpha (@rBCons c x1 a1 f1) (@rBCons c x2 a2 f2)).
Proof.
move : (equi_funprop (@swap_equiv _) alpha_equivariantprop) => /= Requi.
rewrite /alpha /=.
case: (eq_comparable c c) => p //.
have -> /= : p = erefl c by apply eq_axiomK.
set z := fresh_in _. 
apply: (equivP andP); apply and_iff_congr => /=.
  by symmetry; apply (rwP eqP).
eapply iff_stepl. by symmetry; apply/new_all.
eapply iff_stepl. exact/(rwP forallP).
apply forall_iff => i.
rewrite alpha_recE ?rdepth_perm; 
  last exact/(@leq_bigmax _ (fun i => rW_depth (f1 i))). 
apply (@some_fresh_new _ _ Requi _ ((x1, f1 i), (x2, f2 i))).
freshTacCtxt z.
repeat (apply/fresh_prod; split) => //.
all: exact/fresh_fun.
Qed.

Lemma alpha_refl : reflexive alpha.
Proof.
elim => [x|c a f IH|c x a f IH]. 
  - exact/alpha_VarP.
  - by apply/alpha_ConsP; split.
  - rewrite alpha_BConsE eqxx /=.
    apply/forallP => i.
    by rewrite alpha_equivariant.
Qed.

Lemma alpha_sym : symmetric alpha.
Proof.
move => t1 t2; rewrite/alpha.
move: {-1}(rW_depth t1) (leqnn (rW_depth t1)) => n.
elim: n t1 t2 => [|n IHn] [x1|c1 a1 f1|c1 x1 a1 f1] [x2|c2 a2 f2|c2 x2 a2 f2] //=.
all: rewrite ltnS => /bigmax_leqP depth_f1_leqn.
all: case: (eq_comparable c1 c2) => p. 
all: case: (eq_comparable c2 c1) => q. 
all: try congruence.
all: have -> : q = sym_eq p by exact/eq_irrelevance.
all: destruct p => /=; rewrite eq_sym; apply andb_id2l => _.
all: apply/eq_forallb => i.
all: rewrite IHn ?rdepth_perm; last exact/depth_f1_leqn.
  rewrite !alpha_recE //; exact/(@leq_bigmax _ (fun i => rW_depth (f2 i))).
set y := fresh_in _. set z := fresh_in _.
rewrite !alpha_recE ?rdepth_perm //; last first.
  exact/(@leq_bigmax _ (fun i => rW_depth (f2 i))).
suff : y = z by move ->.
rewrite/y/z/fresh_in/=; repeat (rewrite/support/=).
by rewrite eq_fset2 -fsetUA [in X in [fset x2;x1] `|` X]fsetUC fsetUA.
Qed.

Lemma alpha_trans : transitive alpha.
move => t2 t1 t3.
move: {-1}(rW_depth t1) (leqnn (rW_depth t1)) => n.
elim: n t1 t2 t3 => [|n IHn] [x1|c1 a1 f1|c1 x1 a1 f1] 
                             [x2|c2 a2 f2|c2 x2 a2 f2] 
                             [x3|c3 a3 f3|c3 x3 a3 f3] //=;
try solve [move => _; apply eq_op_trans].
all: rewrite ltnS => /bigmax_leqP depthf1_leqn.
all: have [/eqP c1_eq_c2 |/eqP c1_neq_c2] := boolP (c1 == c2).
  2: by move/alpha_Cons_eqc.
  3: by move/alpha_BCons_eqc.
all: have [/eqP c2_eq_c3 |/eqP c2_neq_c3] := boolP (c2 == c3).
  2: by move => _ /alpha_Cons_eqc.
  3: by move => _ /alpha_BCons_eqc.
all: subst.
  move/alpha_ConsP => [a1_eq_a2 alpha_f1f2] /alpha_ConsP [a2_eq_a3 alpha_f2f3].
  apply/alpha_ConsP; split; first exact/(@eq_trans _ a1 a2 a3).
  move => i. apply/(IHn (f1 i) (f2 i) (f3 i)) => //.
  exact/depthf1_leqn.
move/alpha_BConsP => [a1_eq_a2 /= [S1] HS1] /alpha_BConsP [a2_eq_a3 /= [S2] HS2].
apply/alpha_BConsP; split; first exact/(@eq_trans _ a1 a2 a3).
exists (S1 `|` S2) => a aFS1S2 i.
apply/IHn; first by rewrite rdepth_perm; apply/depthf1_leqn.
  exact/HS1/(fresh_fsetU1 aFS1S2).
exact/HS2/(fresh_fsetU2 aFS1S2).
Qed.

End AlphaEquivalence.

Section Quotient.

Canonical alpha_equiv := 
  EquivRel alpha alpha_refl alpha_sym alpha_trans. 

Definition W := {eq_quot alpha}.
Definition W_eqMixin := [eqMixin of W].
Canonical W_eqType := EqType W W_eqMixin.
Canonical W_choiceType := Eval hnf in [choiceType of W].
Canonical W_countType := Eval hnf in [countType of W].
Canonical W_quotType := Eval hnf in [quotType of W].
Canonical W_eqQuotType := Eval hnf in 
      [eqQuotType alpha of W].

Lemma alpha_eqE t t' : alpha t t' = (t == t' %[mod W]).
Proof. by rewrite piE. Qed.

Lemma pi_reprK {I : finType} (f : I -> W) : \pi_W \o (repr \o f) = f.
Proof.
apply/funext => i /=.
by rewrite reprK.
Qed.

Definition Var x := lift_cst W (rVar x).
Lemma rVarK x : \pi_W (rVar x) = Var x.
Proof. by unlock Var. Qed.

Notation lift_fun cons := 
  (locked (fun f => \pi_W (cons (fun i => (@repr _ W_quotType (f i)))))).

Definition Cons c a := lift_fun (@rCons c a).
Lemma rConsK c a f : \pi_W (@rCons c a f) = @Cons c a (\pi \o f).
Proof.
unlock Cons; apply/eqP. 
rewrite [_ == _]piE. apply/alpha_ConsP; split => // i.
by rewrite alpha_eqE reprK.
Qed.

Definition BCons c x a := lift_fun (@rBCons c x a).
Lemma rBConsK c x a f : \pi_W (@rBCons c x a f) = @BCons c x a (\pi \o f).
Proof.
unlock BCons; apply/eqP.
rewrite [_ == _]piE alpha_BConsE eqxx /=. 
apply/forallP => i.
by rewrite alpha_equivariant alpha_eqE reprK.
Qed.

End Quotient.

Section NominalW.

Implicit Types (π : {finperm atom}).

Definition W_act π (t : W) := \pi_W (π \dot repr t).

Lemma W_act1 : W_act (1 atom) =1 id.
Proof. move => t /=. by rewrite /W_act act1 reprK. Qed.

Lemma W_act_equiv π t : 
  π \dot (repr t) == repr (W_act π t) %[mod W].   
Proof. by rewrite /W_act reprK. Qed.

Lemma W_actM π π' t : W_act (π * π') t = W_act π (W_act π' t).
Proof.
apply/eqP. 
by rewrite /W_act actM piE alpha_equivariant alpha_eqE reprK. 
Qed.

Lemma W_actproper : 
  forall t1 t2 π, t1 = t2 -> (W_act π t1) = (W_act π t2).
Proof. by move => t1 t2 π ->. Qed.

Definition W_nominal_setoid_mixin :=
  @PermSetoidMixin W (@eq W) atom W_act W_act1 W_actM W_actproper.

Lemma W_act_id π t :
     (forall a : atom, a \in rW_support (repr t) -> π a = a) -> 
     W_act π t = t.
Proof.
rewrite/W_act => Hact_id.
by rewrite act_id // reprK. 
Qed.

Definition W_nominal_mixin :=
  @NominalMixin W_choiceType atom W_nominal_setoid_mixin _ W_act_id.

Canonical W_nominalType := @NominalType atom W_choiceType W_nominal_mixin.

End NominalW.

Section VariousLemmas.

Lemma pi_equivariant π (t : rW) : 
  π \dot (\pi_W t) = \pi_W (π \dot t).
Proof.
apply/eqmodP => /=. 
by rewrite alpha_equivariant alpha_eqE reprK. 
Qed.

Lemma repr_equivariant π (t : W) : repr (π \dot t) == π \dot (repr t) %[mod W]. 
Proof. by rewrite -pi_equivariant !reprK. Qed.

Lemma Var_equivariant π x : π \dot (Var x) = Var (π x).
Proof. by rewrite -rVarK pi_equivariant /= rVarK. Qed.

Lemma Cons_equivariant π c a f : 
  π \dot (@Cons c a f) = @Cons c a (π \dot f).
Proof.
unlock Cons. 
rewrite pi_equivariant !rConsK. 
congr Cons.
apply/funext => i /=.
exact/sym_eq/eqP/repr_equivariant.
Qed.

Lemma BCons_equivariant π c x a f :
  π \dot (@BCons c x a f) = @BCons c (π x) a (π \dot f).
Proof.
unlock BCons. 
rewrite pi_equivariant !rBConsK.
congr BCons.
apply/funext => i /=.
exact/sym_eq/eqP/repr_equivariant.
Qed.

Lemma fresh_repr x (t : W) : x # (repr t) -> x # t.
Proof.
move => [S [xNS S_supp_t]].
exists S; split => //.
move => π H. by rewrite -[t]reprK pi_equivariant (S_supp_t π) //.
Qed.

Lemma fresh_pi x t : x # t -> x # (\pi_W t).
Proof.
move => [S [xNS S_supp_t]].
exists S; split => //.
move => π H. by rewrite pi_equivariant (S_supp_t π).
Qed.

Lemma fresh_fun_pi {I : finType} x (f : I -> rW) : 
  x # f -> x # (\pi_W \o f).
Proof.
move => xF.
apply (@CFN_principle (fresh_in (\pi_W \o f, f))); first by freshTac.
apply/funext => i /=.
rewrite ffunactE pi_equivariant act_fresh //.
  exact/fresh_fun.
by apply/fresh_fun; freshTac.
Qed.

Lemma eq_BConsE c x1 x2 a1 a2 f1 f2 :
  @BCons c x1 a1 f1 = @BCons c x2 a2 f2 ->
  a1 = a2 /\
  forall z, z # (x1, x2, f1, f2) ->
             swap x1 z \dot f1 = swap x2 z \dot f2.
Proof.
unlock BCons => /eqP.
rewrite -alpha_eqE alpha_BConsE => /andP [/eqP ->] /=. 
set z := fresh_in _ => /forallP Halpha.
split => // z'.
repeat(move/fresh_prod; case); move => *.
apply/(@act_inj _ _ (swap z z'))/funext => i.
freshTacCtxt z.
rewrite [LHS]act_conj [RHS]act_conj !tfinpermR !tfinperm_fresh //.
rewrite ![swap z z' \dot _]act_fresh.
  by move: (Halpha i); rewrite alpha_eqE -!pi_equivariant !reprK => /eqP.
1: apply/fresh_repr; change (z # (repr \o f2) i).
3: apply/fresh_repr; change (z # (repr \o f1) i).
all:exact/fresh_fun.
Qed.

Lemma VarK x : repr (Var x) = rVar x. 
Proof.
have : alpha (repr (Var x)) (rVar x). 
  by rewrite alpha_eqE reprK rVarK. 
by case: (repr (Var x)) => // ? /eqP ->. 
Qed.

Lemma ConsK c a f  : exists f', repr (@Cons c a f) = @rCons c a f' /\ (f = \pi \o f').
Proof.
have: alpha (repr (@Cons c a f)) (@rCons c a (repr \o f)).
  by rewrite alpha_eqE reprK rConsK pi_reprK. 
case: (repr (Cons _ _)) => //= c2 a2 f2. 
have [/eqP c_eq_c2|/eqP c_neq_c2 /alpha_Cons_eqc] := boolP (c == c2);
    last by congruence.
subst.
move/alpha_ConsP => [a2_eq_a f2_alpha_reprf].
exists f2. rewrite a2_eq_a. split => //.
apply/funext => i /=.
move: (f2_alpha_reprf i).
by rewrite alpha_eqE reprK => /eqP.
Qed.

Lemma BConsK c x a f : exists (y : atom) f',
   repr (@BCons c x a f) = @rBCons c y a f'.
Proof.
have: alpha (repr (@BCons c x a f)) (@rBCons c x a (repr \o f)).
  by rewrite alpha_eqE reprK rBConsK pi_reprK.  
case: (repr (BCons _ _ _)) => //= c2 x2 a2 f2. 
have [/eqP c_eq_c2|/eqP c_neq_c2 /alpha_BCons_eqc] := boolP (c == c2);
    last by congruence.
subst.
move/alpha_BConsP => [a2_eq_a _].
exists x2; exists f2.
by rewrite a2_eq_a.
Qed.


Lemma Var_inj : injective Var.
Proof. 
move => x y /(congr1 repr). rewrite !VarK => H. by injection H. Qed.

Lemma Cons_inj c a1 a2 f1 f2 :
  @Cons c a1 f1 = @Cons c a2 f2 -> a1 = a2 /\ f1 = f2.
Proof.
move/(congr1 repr).
have [f1' [-> ->]] := @ConsK c a1 f1.
have [f2' [-> ->]] := @ConsK c a2 f2.
move => H; injection H.
move/eq_sigT_sig_eq => [p].
have -> /= : p = erefl c by apply/eq_axiomK.
move => -> /eq_sigT_sig_eq => [[q]].
have -> /= : q = erefl c by apply/eq_axiomK.
by [].
Qed.

Lemma BConsx_inj c x a1 a2 f1 f2 : 
  (@BCons c x a1 f1 = @BCons c x a2 f2) -> a1 = a2 /\ f1 = f2.
Proof.
pose z := fresh_in (x, f1, f2).
move => /eq_BConsE [a1_eq_2] /(_ z) H.
split => //.
apply/(@act_inj _ _ (swap x z)).
freshTacCtxt z.
apply/H. by repeat (apply/fresh_prod; split).
Qed.

(* Lemma fresh_Var x y : x # (Var y) <-> x # y. *)
(* Proof. *)
(* split => [[S] [xNS S_supp_Ly]|xFy]. *)
(*   exists S; split => // π HS. *)
(*   apply Var_inj. rewrite -Var_equivariant. *)
(*   exact: S_supp_Ly.    *)
(* apply (@CFN_principle (fresh_in (y, Var y))); first by freshTac. *)
(* rewrite Var_equivariant tfinperm_fresh //; by freshTac. *)
(* Qed. *)

(* Lemma fresh_Cons x c a f : x # (@Cons c a f) -> x # a. *)
(* Proof. *)
(* move => [S] [xNS S_supp_caf]. *)
(* exists S; split => // π HS. *)
(* eapply proj2; apply Cons_inj. rewrite -Cons_equivariant. *)
(* exact: S_supp_cl. *)
(* Qed. *)

Lemma fresh_rBCons x y c a f :
  x # (@rBCons c y a f) -> x # (y, f).
Proof.
move => [S] [xNS S_supp_cyl].
exists S; split => // π Hπ.
move: (S_supp_cyl π Hπ) => H.  injection H. 
move => /eq_sigT_sig_eq [p]. 
have -> /= : p = erefl c by apply eq_axiomK.
move => πf_eq_f.
by rewrite prodactE atomactE -{2}πf_eq_f => ->. 
Qed.

Lemma fresh_BCons x y c a f :
  x # y -> x # (@BCons c y a f) -> x # f.
Proof.
move => [S] [xNS S_supp_y] [S'] [xNS' S'_supp_cyf].
exists (S `|` S'); split.
  by rewrite in_fsetU negb_or xNS xNS'.
move => π Hπ. 
apply/(proj2 (@BConsx_inj c y a a _ _ _)).
have y_eq_piy : π y = y.
  apply S_supp_y => b bS. apply Hπ.
  by rewrite in_fsetU bS.
rewrite -{1}y_eq_piy -BCons_equivariant.
apply S'_supp_cyf => b bS'. apply Hπ.
by rewrite in_fsetU bS' orbT.
Qed.
  
Lemma eq_BCons c x y a f :
  y # (x, f) -> @BCons c x a f = @BCons c y a (swap x y \dot f).
Proof.
repeat(move/fresh_prod; case); move => yFx yFf.
unlock BCons. apply/eqmodP. 
rewrite /= alpha_BConsE eqxx /=. 
apply/forallP => i.
rewrite alpha_eqE -!pi_equivariant !reprK.
set z := fresh_in _. freshTacCtxt z.
rewrite act_conj tfinpermL tfinperm_fresh //.
rewrite [swap y z \dot (f i)]act_fresh //; first exact/fresh_fun.
apply/fresh_repr. change (z # ((repr \o f) i)).
exact/fresh_fun.
Qed.

Lemma bname_fresh x c a f : x # (@BCons c x a f).
Proof.
pose y := fresh_in (x, f, @BCons c x a f); freshTacCtxt y.
apply (@CFN_principle y) => //.
rewrite BCons_equivariant tfinpermL. 
exact/sym_eq/eq_BCons/fresh_prod.
Qed.

End VariousLemmas.

Section Depth.

Definition depth (t : W) := rW_depth (repr t).

Lemma rdepth_alpha t u : alpha t u -> rW_depth t = rW_depth u. 
Proof.
elim: t u => [x1|c1 a1 f1 IHf1|c1 x1 a1 f1 IHf1] [x2|c2 a2 f2|c2 x2 a2 f2] //=.
all: have [/eqP c1_eq_c2|/eqP c1_neq_c2] := boolP (c1 == c2).
  2: by move/alpha_Cons_eqc; congruence.
  3: by move/alpha_BCons_eqc; congruence.  
all: subst.
1: move/alpha_ConsP => [_ alpha_f1_f2].
2: rewrite alpha_BConsE; set z := fresh_in _  => /andP [_ /= /forallP alpha_f1_f2].
all: apply/eq_S/eq_bigr => i _. 
  exact/IHf1.
move: (alpha_f1_f2 i).
rewrite -(alpha_equivariant _ _ (swap x1 z)) -actM tfinperm_idempotent act1 => /IHf1.
by rewrite !rdepth_perm.
Qed.
                                                     
Lemma depth_rdepth t : depth (\pi t) = rW_depth t.
Proof. 
apply rdepth_alpha. by rewrite alpha_eqE reprK.
Qed.

Lemma depth_perm t π : depth (π \dot t) = depth t.
Proof.
rewrite/depth -[RHS](rdepth_perm π).
apply rdepth_alpha. rewrite alpha_eqE.
exact: repr_equivariant.
Qed.

Lemma depth_Var x : depth (Var x) = 0.
Proof. by rewrite/depth VarK. Qed.

Lemma depth_Cons c a f : depth (@Cons c a f) = (\max_i (depth (f i))).+1.
Proof. unlock Cons. by rewrite depth_rdepth /=. Qed.

Lemma depth_BinderCons c x a f : 
  depth (@BCons c x a f) = (\max_i (depth (f i))).+1.
Proof. unlock BCons. by rewrite depth_rdepth /=. Qed.

End Depth.

Section EliminationPrinciples.

Lemma W_naive_ind (P : W -> Prop) :
  (forall x, P (Var x)) ->
  (forall c a f, (forall i, P (f i)) -> P (@Cons c a f)) ->
  (forall c x a f, (forall i, P (f i)) -> P (@BCons c x a f)) ->
  forall u, P u.
Proof. 
move => HVar HCons HBCons u; rewrite -[u]reprK.
elim: (repr u) => [x|c a f IHf|c x a f IHf] /=.
  - by rewrite rVarK.              
  - rewrite rConsK. exact/HCons.
  - rewrite rBConsK. exact/HBCons.
Qed.

Lemma W_ind {env : nominalType atom} (C : env) (P : W -> Prop) :
  (forall x, P (Var x)) ->
  (forall c a f, (forall i, P (f i)) -> P (@Cons c a f)) ->
  (forall c x a f, x # C -> (forall i, P (f i)) -> P (@BCons c x a f)) ->
  forall u, P u.
Proof. 
move => HVar HCons HBcons u.
suff : forall π, P (π \dot u).
  by move => /(_ (1 atom)); rewrite act1.
elim/W_naive_ind : u => [x|c a f IHf|c x a f IHf] π.
  - by rewrite Var_equivariant.
  - rewrite Cons_equivariant. apply/HCons => i. 
    by rewrite ffunactE. 
  - rewrite BCons_equivariant. 
    pose z := fresh_in (C, π x, π \dot f); freshTacCtxt z.
    rewrite (@eq_BCons _ _ z) -?actM => //; last exact/fresh_prod.
    apply HBcons => // i.
    by rewrite ffunactE. 
Qed.

Context (X : nominalType atom)
        (f_var : atom -> X)
        (f_cons : forall (c : cons_label), (cons_annot c) -> 
                                           ('I_(cons_arity c) -> W) -> 
                                           ('I_(cons_arity c) -> X) -> X)
        (f_bcons : forall (c : bcons_label), atom -> 
                                             (bcons_annot c) ->
                                             ('I_(bcons_arity c) -> W) -> 
                                             ('I_(bcons_arity c) -> X) -> X)
        (Supp : {fset atom})
        (dflt : X).

Hypothesis f_var_equivariant : 
  forall (π : {finperm atom}) x, 
    [disjoint finsupp π & Supp] -> π \dot f_var x = f_var (π \dot x).

Hypothesis f_cons_equivariant :
  forall (π : {finperm atom}) c a f f',
    [disjoint finsupp π & Supp] ->
                  π \dot @f_cons c a f f' = 
                  @f_cons c a (π \dot f) (π \dot f').

Hypothesis f_bcons_equivariant :
  forall (π : {finperm atom}) c x a f f', 
    [disjoint finsupp π & Supp] -> π \dot @f_bcons c x a f f' = 
                                   @f_bcons c (π x) a (π \dot f) (π \dot f').                 

Hypothesis FCB_fbcons :
  forall x c a f f', x # Supp -> x # (@f_bcons c x a f f').


Fixpoint W_rect_rec (n : nat) (t : W):=
  match n, (repr t) with
    |_, rVar x => f_var x
    |S n, rCons c a f => @f_cons c a (\pi \o f) ((W_rect_rec n) \o \pi \o f)
    |S n, rBCons c x a f =>
     let z := fresh_in (Supp, @rBCons c x a f) in
     @f_bcons c z a
             (swap x z \dot (\pi_W \o f))
             ((W_rect_rec n) \o (swap x z \dot (\pi_W \o f)))
    |_, _ => dflt
  end.

Definition W_rect t := W_rect_rec (depth t) t.

Lemma W_rect_recE n t : depth t <= n -> W_rect_rec n t = W_rect t.
Proof.
rewrite/W_rect; move: {-2}n (leqnn n).
elim: n t => [|n IHn] t //; rewrite /depth. 
  by move => ?; do 2?(rewrite leqn0 => /eqP ->).
move => [?|m]; first by rewrite leqn0 => /eqP ->.
rewrite ltnS => m_leq_n.
case_eq (repr t) => [x|c a f|c x a f] /= -> //.
all: rewrite ltnS => /bigmax_leqP IHf; try (congr f_cons); try (congr f_bcons).
all: apply/funext => i /=.
all: rewrite IHn // ?depth_perm ?depth_rdepth; last exact/IHf.
all: rewrite [RHS]IHn; first by rewrite ?depth_perm depth_rdepth.
1: apply/(@leq_trans m) => //; exact/bigmax_leqP.
2: apply/(@leq_trans m) => //; exact/bigmax_leqP. (* factorisation ?*)
all: rewrite ?depth_perm depth_rdepth. 
all: exact/leq_bigmax_cond.
Qed.

Lemma W_rect_VarE x : W_rect (Var x) = f_var x.
Proof. by rewrite /W_rect depth_Var /= VarK. Qed.

Lemma W_rect_ConsE c a f : 
  W_rect (@Cons c a f) = @f_cons c a f (W_rect \o f).
Proof.
rewrite/W_rect depth_Cons /=.
have [f' [-> ->]] := @ConsK c a f.
congr f_cons => //.
apply/funext => i /=.
apply W_rect_recE => /=. 
exact/leq_bigmax_cond.
Qed.

Lemma W_rect_BConsE_subproof c x a f :
  let z := (fresh_in (Supp, repr (@BCons c x a f))) in
    W_rect (@BCons c x a f) = 
    @f_bcons c z a (swap x z \dot f) (W_rect \o (swap x z \dot f)).
have [y [f'] repr_cxf] := @BConsK c x a f => /=.
rewrite /W_rect depth_BinderCons /= repr_cxf.
set z := fresh_in _.
suff : swap y z \dot (\pi_W \o f') = swap x z \dot f.
  move => ->. congr f_bcons.
  apply/funext => i /=.
  rewrite W_rect_recE // depth_perm.
  exact/leq_bigmax_cond.
move: (congr1 \pi_W repr_cxf).
rewrite reprK rBConsK => /eq_BConsE [_] /(_ z) H.
have : z # (@rBCons c y a f') by freshTac.
move => /fresh_rBCons. repeat (move/fresh_prod; case); move => *.
have [/eqP z_eq_x|/fresh_atomP ?] := boolP (z == x).
  rewrite z_eq_x tfinperm_id act1.
  move: (congr1 \pi_W repr_cxf); rewrite reprK rBConsK.
  rewrite [X in _ = X](@eq_BCons c y x a) -?z_eq_x //; last first.
    apply/fresh_prod; split => //.
    exact/fresh_fun_pi.
  by move/BConsx_inj => [_] ->.
apply/sym_eq/H. repeat(apply/fresh_prod; split) => //; last exact/fresh_fun_pi.
apply/(@fresh_BCons _ x c a f) => //.
apply/fresh_repr. rewrite repr_cxf.
by freshTac.
Qed.

Definition equiv t := 
  forall (π : {finperm atom}), [disjoint finsupp π & Supp] ->
                               π \dot (W_rect t) = 
                               W_rect (π \dot t).

Definition res c x a f := W_rect (@BCons c x a f) =
                        @f_bcons c x a f (W_rect \o f).

Lemma equiv_res_subproof c x a f :
(forall i, equiv (f i)) ->
x # Supp -> @res c x a f.
Proof.
move => Hequiv xFSupp.
rewrite /res W_rect_BConsE_subproof; set y := fresh_in _.
set rhs := RHS; set lhs := LHS; rewrite /lhs/rhs.
set b := fresh_in (lhs, rhs, Supp, f, x). 
freshTacCtxt b. freshTacCtxt y.
rewrite -[LHS](@act_fresh _ y b) //; last exact/FCB_fbcons.
rewrite -[RHS](@act_fresh _ x b) //; last exact/FCB_fbcons.
rewrite !f_bcons_equivariant;
  try solve [exact/disjoint_tfsupp]. 
rewrite !tfinpermL.
have : y # @BCons c x a f by apply/fresh_repr.
have [/eqP ->|/fresh_atomP zFx /(fresh_BCons zFx) ?] := boolP (y == x).
  by rewrite tfinperm_id !act1.
rewrite ![swap y b \dot _ \dot _]act_conj !tfinpermL !tfinperm_fresh //.
rewrite [swap y b \dot f]act_fresh //.
congr f_bcons.
apply/funext => i /=.
rewrite !ffunactE /= -Hequiv; last exact/disjoint_tfsupp.
rewrite act_conj tfinpermL tfinperm_fresh //.
rewrite Hequiv; last exact/disjoint_tfsupp. 
rewrite [swap y b \dot _]act_fresh //.
all: exact/fresh_fun.
Qed.

Lemma W_rect_equivariant t :
 equiv t.
Proof.
elim/(@W_ind _ Supp): t => [v|c a f IHf|c z a f zFSupp IHf] π disj_pi_S.
  - by rewrite Var_equivariant !W_rect_VarE f_var_equivariant.
  - rewrite !Cons_equivariant !W_rect_ConsE f_cons_equivariant //. 
    congr f_cons.
    apply/funext => i.
    by rewrite !ffunactE /= IHf . 
  - have Hres1 := (@equiv_res_subproof c _ _ _ IHf zFSupp).
    have Hres2 : @res c (π z) a (π \dot f).
      apply/equiv_res_subproof => //; last exact/disj_im_fresh. 
      move => i π' ? /=.
      rewrite -actM -!IHf // ?actM //; exact/disjoint_conj.
    rewrite BCons_equivariant Hres1 Hres2. 
    rewrite f_bcons_equivariant //. 
    congr f_bcons.
    apply/funext => i /=.
    by rewrite ffunactE IHf.
Qed.

Lemma W_rect_BConsE c x a f : 
  x # Supp -> 
  W_rect (@BCons c x a f) = @f_bcons c x a f (W_rect \o f).
Proof.
move => xFsupp.
apply/equiv_res_subproof => // ? ?. 
exact/W_rect_equivariant.
Qed.

End EliminationPrinciples.

Section Substitution.

Context (x : atom) (t : W) (dflt := Var 0).
Notation Supp := (x |` support t).

(* substitution de x par t *)

Definition subst_var (y : atom) :=
  if x == y then t else Var y.
Definition subst_cons (c : cons_label) a (f : 'I_(cons_arity c) -> W) res :=
  @Cons c a res.
Definition subst_bcons (c : bcons_label) (y : atom) a
           (f : 'I_(bcons_arity c) -> W) res :=
  @BCons c y a res.

Definition subst := 
  @W_rect _ subst_var subst_cons subst_bcons Supp dflt.

Lemma subst_var_equiv (π : {finperm atom}) y : 
  [disjoint finsupp π & Supp] -> 
  π \dot subst_var y = subst_var (π y). 
Proof.
rewrite fdisjoint_sym fdisjointU1X => /andP [/finsfun_dflt pix_x disj_pi_Supp].
rewrite /subst_var if_equivariant -{2}pix_x (inj_eq (@finperm_inj _ π)).
by rewrite fresh_perm // Var_equivariant.
Qed.
  
Lemma subst_cons_equiv (π : {finperm atom}) c a f f' :
    [disjoint finsupp π & Supp] ->
                  π \dot @subst_cons c a f f' = 
                  @subst_cons c a (π \dot f) (π \dot f').
Proof. by rewrite /subst_cons Cons_equivariant. Qed.

Lemma subst_bcons_equiv (π : {finperm atom}) c y a f f' :
    [disjoint finsupp π & Supp] -> 
    π \dot @subst_bcons c y a f f' = 
    @subst_bcons c (π y) a (π \dot f) (π \dot f').    
Proof. by rewrite /subst_bcons BCons_equivariant. Qed.

Lemma FCB y c a f f' : y # Supp -> y # (@subst_bcons c y a f f').
Proof. rewrite/subst_bcons => ?. exact/bname_fresh. Qed.

Lemma subst_VarE y : subst (Var y) = if x == y then t else Var y.
Proof. by rewrite /subst W_rect_VarE /subst_var. Qed.

Lemma subst_ConsE c a f : subst (@Cons c a f) = @Cons c a (subst \o f).
Proof. by rewrite /subst W_rect_ConsE /subst_cons. Qed.

Lemma subst_BConsE c y a f : 
  y # x -> y # t -> 
  subst (@BCons c y a f) = @BCons c y a (subst \o f).
Proof.
move => yFx yFt.
apply W_rect_BConsE.
  - exact/subst_var_equiv.
  - exact/subst_cons_equiv.
  - exact/subst_bcons_equiv.
  - exact/FCB.
(* remplacer Supp -> env *)
Admitted.

End Substitution.

Notation " t { x := u } " := (subst x u t) (at level 0).

End W.