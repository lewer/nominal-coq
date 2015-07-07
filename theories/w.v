From Ssreflect
Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq fintype.
From MathComp
Require Import finfun finset generic_quotient bigop.

Require Import finmap finsfun finperm nominal utilitaires.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope finperm_scope with fperm.
Local Open Scope finperm_scope.
Local Open Scope fset.
Local Open Scope quotient_scope.

Axiom funext : forall {X : Type} {n : nat} (f g : 'I_n -> X),
                 f =1 g -> f = g.

Import Key.Exports.

Section W.

Context (cons_label : eqType)
        (bcons_label : eqType)
        (cons_annot : cons_label -> nominalType atom)
        (cons_arity : cons_label -> nat)
        (bcons_annot : bcons_label -> nominalType atom)
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
    |rCons c a f => @rCons c (π \dot a) (fun i => rW_act π (f i))
    |rBCons c x a f => @rBCons c (π x) (π \dot a) (fun i => rW_act π (f i))
  end.

Lemma rW_act1 : rW_act (1 atom) =1 id.
Proof. 
elim => [x|c a f IH|c x a f IH] /=.
  - by rewrite finsfun1.
  - congr rCons; first exact/act1.
    exact/funext/IH.
  - rewrite finsfun1 act1. congr rBCons.
    exact/funext/IH.
Qed.

Lemma rW_actM π π' (t : rW) : 
  rW_act (π * π') t = rW_act π (rW_act π' t).
Proof.
elim : t => [x|c a f IH|c x a f IH] /=.
  - by rewrite finsfunM.
  - rewrite actM. congr rCons.
    exact/funext/IH.
  - rewrite finsfunM actM. congr rBCons.
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
    |rCons c a f => support a `|` 
                    \fbigcup_ (i in 'I_(cons_arity c)) (rW_support (f i))
    |rBCons c x a f => x |` ((support a) `|`
                       \fbigcup_(i in 'I_(bcons_arity c)) (rW_support (f i)))
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
  - rewrite act_id; last first.
      move => x x_supp_a. apply/Hsupp. by rewrite in_fsetU x_supp_a.
    congr rCons.
    apply/funext => i. apply/IH => x x_supp_fi.
    apply/Hsupp/fsetUP; right.
    apply/fbigcupP. by exists i.
  - rewrite Hsupp; last exact/fset1U1.
    rewrite act_id; last first.
      move => y y_supp_a. apply/Hsupp.
      apply/fset1Ur. by rewrite in_fsetU y_supp_a.
    congr rBCons.
    apply/funext => i. apply/IH => y y_supp_fi.
    apply/Hsupp; do 2 (apply/fsetUP; right).
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
                     let z := fresh_in (x1, x2, [seq f1 i | i : 'I_m], [seq f2 i | i : 'I_m]) in
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
all: rewrite (inj_eq (@act_inj _ _ π)); apply andb_id2l => _. 
all: apply eq_forallb => i.
  exact/IHn/IHl1.
set z := fresh_in _; set y := fresh_in _.
rewrite -act_conj_imL -[X in alpha_rec _ _ X]act_conj_imL.
rewrite IHn; try rewrite -[RHS](@IHn _ _ (swap y (π^-1 z)));
  try solve [rewrite rdepth_perm; exact: IHl1]. 
freshTacCtxt z; freshTacCtxt y.
rewrite -{1}[f1 i](@act_fresh _ y (π^-1 z)) //; last first.
  apply/fresh_map/im_inv_fresh; by rewrite listactE -map_comp.  
  exact/fresh_map. 
rewrite -{1}[f2 i](@act_fresh _ y (π^-1 z)) //; last first.
  apply/fresh_map/im_inv_fresh; by rewrite listactE -map_comp.  
  exact/fresh_map. 
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
all: exact/fresh_map.
Qed.

Lemma alpha_refl : reflexive alpha.
Proof.
elim => [x|c a f IH|c x a f IH]. 
  - exact/alpha_VarP.
  - by apply/alpha_ConsP; split.
  - apply/alpha_BConsP; split => //=.
    exists fset0 => b _ i. 
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
by rewrite eq_fset2 -fsetUA [list_support _ `|` list_support _]fsetUC fsetUA.
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

(* Lemma all2_alpha_eq l1 l2 :  *)
(*   all2 alpha l1 l2 ->  *)
(*   map \pi_W l1 = map \pi_W l2.  *)
(* Proof. *)
(* move => /all2P alpha_l1l2. apply/all2_prop_eq/all2_prop_map. *)
(* move : alpha_l1l2; apply eq_in_all2_prop => t1 t2 t1s1 t2s2. *)
(* rewrite alpha_eqE.  *)
(* by split; move/eqP. *)
(* Qed. *)

Definition Var x := lift_cst W (rVar x).
Lemma rVarK x : \pi_W (rVar x) = Var x.
Proof. by unlock Var. Qed.

Notation lift_map cons := 
  (locked (fun f => \pi_W (cons (fun i => (@repr _ W_quotType (f i)))))).

Definition Cons c a := lift_map (@rCons c a).
Lemma rConsK c a f : \pi_W (@rCons c a f) = @Cons c a (\pi \o f).
Proof.
unlock Cons; apply/eqP. 
rewrite [_ == _]piE. apply/alpha_ConsP; split => // i.
by rewrite alpha_eqE reprK.
Qed.

Definition BinderCons c x := lift_map (rBinderCons c x).
Lemma rBinderConsK c x l : \pi_W (rBinderCons c x l) = BinderCons c x (map \pi_W l).
Proof.
unlock BinderCons; apply/eqP.
rewrite [_ == _]piE alphaE eqxx /=. 
rewrite all2_equivariant; 
  last by move => ? ? ?; rewrite alpha_equivariant.
rewrite -map_comp all2_mapr. apply all2_refl => t _ /=.
by rewrite alpha_eqE reprK.
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

Lemma Annot_equivariant π x : π \dot (Annot x) = Annot (π \dot x).
Proof. by rewrite -rAnnotK pi_equivariant /= rAnnotK. Qed.

Lemma Cons_equivariant π c l : 
  π \dot (Cons c l) = Cons c (π \dot l).
Proof.
unlock Cons. rewrite pi_equivariant !rConsK -!map_comp. 
congr Cons.
apply/sym_eq/eq_map => t /=.
exact/eqP/repr_equivariant.
Qed.

Lemma BinderCons_equivariant π c x l :
  π \dot (BinderCons c x l) = BinderCons c (π x) (π \dot l).
Proof.
unlock BinderCons. rewrite pi_equivariant !rBinderConsK -!map_comp.
congr BinderCons.
apply/sym_eq/eq_map => t /=.
exact/eqP/repr_equivariant.
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

Lemma fresh_list_repr x (l : seq W) : x # (map repr l) -> x # l.
Proof.
move => ?.
apply fresh_list => ? /(map_f (@repr rW W_quotType)) ?. 
apply fresh_repr; by freshTacList.
Qed.

Lemma fresh_list_pi x l : x # l -> x # (map \pi_W l).
move => ?.
apply fresh_list => ? /mapP [?] ? ->.
apply fresh_pi. by freshTacList.
Qed.

Lemma eq_BConsE c x1 x2 l1 l2 :
  BinderCons c x1 l1 = BinderCons c x2 l2 ->
  forall z, z # x1 -> z # x2 -> z # l1 -> z # l2 -> 
             swap x2 z \dot l2 = swap x1 z \dot l1.
Proof.
unlock BinderCons => /eqP. 
rewrite -alpha_eqE alphaE eqxx /= => /all2_alpha_eq.
set z := fresh_in _. 
rewrite -!map_equivariant;
  try solve [move => *; exact: pi_equivariant].
rewrite !mapK;
  try solve [move => *; exact: reprK].
move => x1zl1_x2zl2 z' *.
freshTacCtxt z.
apply (@act_inj _ _ (swap z z')).
rewrite [in LHS]act_conj [in RHS]act_conj !tfinpermR !tfinperm_fresh //. 
rewrite ![swap z z' \dot _]act_fresh //.
all: exact: fresh_list_repr.
Qed.

Lemma VarK x : repr (Var x) = rVar x. 
Proof.
have : alpha (repr (Var x)) (rVar x). 
  by rewrite alpha_eqE reprK rVarK. 
by case: (repr (Var x)) => // ? /eqP ->. 
Qed.

Lemma AnnotK x : repr (Annot x) = rAnnot x. 
Proof.
have : alpha (repr (Annot x)) (rAnnot x). 
  by rewrite alpha_eqE reprK rAnnotK. 
by case: (repr (Annot x)) => // ? /eqP ->. 
Qed.

Lemma ConsK c l : exists repr_l,
    l = map \pi_W repr_l /\ repr (Cons c l) = rCons c repr_l.
Proof.
have: alpha (repr (Cons c l)) (rCons c (map repr l)).
  rewrite alpha_eqE reprK rConsK -map_comp map_id_in //. 
  move => t _ /=. by rewrite reprK.
case: (repr (Cons _ _)) => //= c2 l2;
rewrite alphaE // => /andP [/eqP c2_eq_c] => /all2_alpha_eq. 
rewrite -map_comp map_id_in => pil2_ll1; 
  last by move => _ /=; rewrite reprK.
by exists l2; split; last by rewrite c2_eq_c.
Qed.

Lemma BConsK c (x : atom) (l : seq W) : exists (y : atom) (repr_l : seq rW),
   repr (BinderCons c x l) = rBinderCons c y repr_l.
Proof.
have: alpha (repr (BinderCons c x l)) (rBinderCons c x (map repr l)).
  rewrite alpha_eqE reprK rBinderConsK -map_comp map_id_in //. 
  move => t _ /=. by rewrite reprK.
case: (repr (BinderCons _ _ _)) => //= c2 x2 l2.
rewrite alphaE => /andP [/eqP ->] /= H. 
by exists x2; exists l2. 
Qed.

Lemma W_caseP (t : W) :
  (exists x, t = Var x) \/
  (exists x, t = Annot x) \/
  (exists c l, t = Cons c l) \/
  (exists c x l, t = BinderCons c x l).
Proof.
case_eq (repr t) => [x|a|c l|c x l] /(congr1 \pi_W).
all: rewrite reprK (rVarK, rAnnotK, rConsK, rBinderConsK) => ?.
  - left. by exists x.                                                            
  - right; left. by exists a.
  - right; right; left. by exists c; exists (map \pi l).
  - right; right; right. by exists c; exists x; exists (map \pi l).
Qed.

Lemma Var_inj : injective Var.
Proof. 
move => x y /(congr1 repr). rewrite !VarK => H. by injection H. Qed.

Lemma Annot_inj : injective Annot.
Proof. 
move => x y /(congr1 repr). rewrite !AnnotK => H. by injection H. Qed.

Lemma Cons_inj c1 c2 l1 l2 : 
  Cons c1 l1 = Cons c2 l2 -> c1 = c2 /\ l1 = l2.
Proof.
move/(congr1 repr). 
have [reprl1 [-> ->]] := ConsK c1 l1.
have [reprl2 [-> ->]] := ConsK c2 l2.
move => H.
by injection H => -> ->. 
Qed.

Lemma BConsx_inj c x : injective (BinderCons c x).
Proof.
move => l1 l2; 
pose z := fresh_in (x, l1, l2). 
move => /eq_BConsE /(_ (fresh_in (x, l1, l2))) H.
apply/(@act_inj _ _ (swap x z))/sym_eq.
freshTacCtxt z.
exact/H.
Qed. 

Lemma fresh_Var x y : x # (Var y) <-> x # y.
Proof.
split => [[S] [xNS S_supp_Ly]|xFy].
  exists S; split => // π HS.
  apply Var_inj. rewrite -Var_equivariant.
  exact: S_supp_Ly.   
apply (@CFN_principle (fresh_in (y, Var y))); first by freshTac.
rewrite Var_equivariant tfinperm_fresh //; by freshTac.
Qed.

Lemma fresh_Annot x y : x # (Annot y) <-> x # y.
Proof.
split => [[S] [xNS S_supp_Ly]|xFy].
  exists S; split => // π HS.
  apply Annot_inj. rewrite -Annot_equivariant.
  exact: S_supp_Ly.   
apply (@CFN_principle (fresh_in (y, Annot y))); first by freshTac.
rewrite Annot_equivariant act_fresh //; by freshTac.
Qed.

Lemma fresh_Cons x c l : x # (Cons c l) -> x # l.
Proof.
move => [S] [xNS S_supp_cl].
exists S; split => // π HS.
eapply proj2; apply Cons_inj. rewrite -Cons_equivariant.
exact: S_supp_cl.
Qed.

Lemma fresh_rBCons x y c (l : seq rW) : 
  x # (rBinderCons c y l) -> x # y /\ x # l.
Proof.                             
move => [S] [xNS S_supp_cyl].
split; exists S; split => // π Hπ.
all: by move: (S_supp_cyl π Hπ) => /= H; injection H => *.
Qed.

Lemma fresh_BCons x y c l : 
  x # y -> x # (BinderCons c y l) -> x # l.
Proof.
move => [S] [xNS S_supp_y] [S'] [xNS' S'_supp_cyl].
exists (S `|` S'); split.
  by rewrite in_fsetU negb_or xNS xNS'.
move => π Hπ. 
apply/(@BConsx_inj c y).
have y_eq_piy : π y = y.
  apply S_supp_y => a aS. apply Hπ.
  by rewrite in_fsetU aS.
rewrite -{1}y_eq_piy -BinderCons_equivariant.
apply S'_supp_cyl => a aS'. apply Hπ.
by rewrite in_fsetU aS' orbT.
Qed.
  
Lemma eq_BCons c x y l :
  y # x -> y # l -> BinderCons c x l = BinderCons c y (swap x y \dot l).
Proof.
move => xFy xFl.
unlock BinderCons; apply/eqmodP => /=.
rewrite alphaE eqxx /= !all2_map all2_mapr. 
apply all2_refl => t tl; set z := fresh_in _; freshTacCtxt z.
rewrite alpha_eqE -!pi_equivariant !reprK.
rewrite act_conj tfinpermL tfinperm_fresh //.
rewrite [swap y z \dot t]act_fresh //; first by freshTacList.
move: tl => /(map_f (@repr rW W_quotType)) /= ?.
apply fresh_repr; by freshTacList.
Qed.

Lemma bname_fresh x c l : x # (BinderCons c x l).
Proof.
pose y := fresh_in (x, l, BinderCons c x l); freshTacCtxt y.
apply (@CFN_principle y) => //.
rewrite BinderCons_equivariant tfinpermL.
exact/sym_eq/eq_BCons.
Qed.

End VariousLemmas.

Section Depth.

Definition depth (t : W) := rW_depth (repr t).

Lemma rdepth_alpha t u : alpha t u -> rW_depth t = rW_depth u. 
Proof.
elim/rW_better_ind: t u => [x1|a1|c1 l1 IHl1|c1 x1 l1 IHl1] [x2|a2|c2 l2|c2 x2 l2] //=.
all: rewrite alphaE => /andP /= [_ l1_alpha_l2].
all: apply eq_S; congr maxlist.
  apply (@all2_quot _ _ _ _ alpha) => // x y xl1 yl2. 
  exact/IHl1.
eapply (@all2_quot _ _ _ _ ); last by 
  move: l1_alpha_l2; rewrite all2_map; exact: id.
move => t1 t2 t1l1 t2l2 /=; set z:= fresh_in _.
rewrite -(alpha_equivariant _ _ (swap x1 z)) -actM tfinperm_idempotent act1.
by move/IHl1; rewrite !rdepth_perm; auto.
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

Lemma depth_Annot x : depth (Annot x) = 0.
Proof. by rewrite/depth AnnotK. Qed.

Lemma depth_Cons c l : depth (Cons c l) = (maxlist (map depth l)).+1.
Proof.
unlock Cons. rewrite depth_rdepth /=.
apply/eq_S; congr maxlist.
rewrite  -map_comp. exact/eq_map.
Qed.

Lemma depth_BinderCons c x l : depth (BinderCons c x l) = (maxlist (map depth l)).+1.
Proof.
unlock BinderCons. rewrite depth_rdepth /=.
apply/eq_S; congr maxlist.
by rewrite -map_comp; apply eq_map => t /=.
Qed.

End Depth.

Section EliminationPrinciples.

Lemma W_naive_ind (P : W -> Prop) :
  (forall x, P (Var x)) ->
  (forall x, P (Annot x)) ->
  (forall c l, (forall t, t \in l -> P t) -> P (Cons c l)) ->
  (forall c x l, (forall t, t \in l -> P t) -> P (BinderCons c x l)) ->
  forall u, P u.
(* {in l, P} ? *)
Proof. 
move => HVar HAnnot HCons HBCons u; rewrite -[u]reprK.
elim/rW_better_ind : (repr u) => [x|a|c l IHl|c x l IHl] /=.
  - by rewrite rVarK.              
  - by rewrite rAnnotK.
  - rewrite rConsK. apply HCons => t /mapP [reprt ?] ->.
    exact/IHl.
  - rewrite rBinderConsK. apply HBCons => t /mapP [reprt ?] ->.
    exact/IHl.
Qed.

Lemma W_ind {env : nominalType atom} (C : env) (P : W -> Prop) :
  (forall x, P (Var x)) ->
  (forall x, P (Annot x)) ->
  (forall c l, (forall t, t \in l -> P t) -> P (Cons c l)) ->
  (forall c x l, x # C -> (forall t, t \in l -> P t) -> P (BinderCons c x l)) ->
  forall u, P u.
(* {in l, P} ? *)
Proof. 
move => HVar HAnnot HCons HBcons u.
suff : forall π, P (π \dot u).
  by move => /(_ (1 atom)); rewrite act1.
elim/W_naive_ind : u => [x|a|c l IHl|c x l IHl] π.
  - by rewrite Var_equivariant.
  - by rewrite Annot_equivariant.
  - rewrite Cons_equivariant. apply HCons => t /mapP [reprt ?] ->. 
    exact/IHl.    
  - rewrite BinderCons_equivariant. 
    pose z := fresh_in (C, π x, π \dot l); freshTacCtxt z.
    rewrite (@eq_BCons _ _ z) -?actM => //.
    apply HBcons => // t /mapP [reprt ?] ->.
    exact/IHl.
Qed.

Context (X : nominalType atom)
        (f_var : atom -> X)
        (f_annot : annot_label -> X)
        (f_cons : cons_label -> seq W -> seq X -> X)
        (f_bcons : bcons_label -> atom -> seq W -> seq X -> X)
        (Supp : {fset atom})
        (dflt : X).

Hypothesis f_var_equivariant : 
  forall (π : {finperm atom}) x, 
    [disjoint finsupp π & Supp] -> π \dot f_var x = f_var (π \dot x).

Hypothesis f_annot_equivariant : 
  forall (π : {finperm atom}) x, 
    [disjoint finsupp π & Supp] -> π \dot f_annot x = f_annot (π \dot x).

Hypothesis f_cons_equivariant :
  forall (π : {finperm atom}) c l l',
    [disjoint finsupp π & Supp] ->
                  π \dot f_cons c l l' = 
                  f_cons c (π \dot l) (π \dot l').

Hypothesis f_bcons_equivariant :
  forall (π : {finperm atom}) c x l l', 
    [disjoint finsupp π & Supp] -> π \dot f_bcons c x l l' = 
                                   f_bcons c (π x) (π \dot l) (π \dot l').                 

Hypothesis FCB_fbcons :
  forall x c l l', x # Supp -> x # (f_bcons c x l l').


Fixpoint W_rect_rec (n : nat) (t : W):=
  match n, (repr t) with
    |_, rVar x => f_var x
    |_, rAnnot x => f_annot x
    |S n, rCons c l => f_cons c (map \pi l) (map (W_rect_rec n) (map \pi l))
    |S n, rBinderCons c x l =>
     let z := fresh_in (Supp, rBinderCons c x l) in
     f_bcons c z
             (swap x z \dot (map \pi_W l))
             (map (W_rect_rec n) (swap x z \dot map \pi_W l))
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
case_eq (repr t) => [x|a|c l|x c l] /= -> //.
all: rewrite ltnS => IHl; try (congr f_cons); try (congr f_bcons).
all: rewrite 2?listactE -!map_comp; apply eq_in_map => u ul /=.
all: rewrite !IHn //; first exact/(@leq_trans m);
     rewrite ?depth_perm depth_rdepth; first exact/in_maxlist /map_f.
all: by eapply leq_trans; first apply/in_maxlist/map_f/ul.
Qed.

Lemma W_rect_VarE x : W_rect (Var x) = f_var x.
Proof. by rewrite /W_rect depth_Var /= VarK. Qed.

Lemma W_rect_AnnotE x : W_rect (Annot x) = f_annot x.
Proof. by rewrite /W_rect depth_Annot /= AnnotK. Qed.

Lemma W_rect_ConsE c l : 
  W_rect (Cons c l) = f_cons c l (map W_rect l).
Proof.
rewrite/W_rect depth_Cons /=.
have [reprl [-> ->]] := ConsK c l.
congr f_cons => //.
rewrite -!map_comp. apply eq_in_map => t /= ?.
apply W_rect_recE => /=. 
exact/in_maxlist/map_f.
Qed.

Lemma W_rect_BConsE_subproof c x l :
  let z := (fresh_in (Supp, repr (BinderCons c x l))) in
    W_rect (BinderCons c x l) = 
    f_bcons c z (swap x z \dot l) (map W_rect (swap x z \dot l)).
have [y [l'] repr_cxl] := BConsK c x l => /=.
rewrite /W_rect depth_BinderCons /= repr_cxl.
set z := fresh_in _. 
suff : swap y z \dot (map \pi_W l') = swap x z \dot l.
  move => ->. congr f_bcons.
  apply eq_in_map => ? /mapP [?] ? ->. 
  rewrite W_rect_recE // depth_perm. exact/in_maxlist/map_f.
move: (congr1 \pi_W repr_cxl).
rewrite reprK rBinderConsK => /eq_BConsE /(_ z) H.
have : z # (rBinderCons c y l') by freshTac.
move => /fresh_rBCons [? /fresh_list_pi ?].
have [/eqP z_eq_x|/fresh_atomP ?] := boolP (z == x).
  rewrite z_eq_x tfinperm_id act1.
  move: (congr1 \pi_W repr_cxl); rewrite reprK rBinderConsK.
  rewrite [X in _ = X](@eq_BCons c y x) -?z_eq_x // => J.  
  exact/BConsx_inj/sym_eq/J.
apply H => //. apply/(@fresh_BCons _ x c) => //.
apply fresh_repr; rewrite repr_cxl. 
by freshTac.
Qed.

Definition equiv t := 
  forall (π : {finperm atom}), [disjoint finsupp π & Supp] ->
                               π \dot (W_rect t) = 
                               W_rect (π \dot t).

Definition res c x l := W_rect (BinderCons c x l) =
                        f_bcons c x l (map W_rect l).

Lemma equiv_res_subproof c x (l : seq W) :
(forall (t : W), t \in l -> equiv t) ->
x # Supp -> res c x l.
Proof.
move => Hequiv zFSupp.
rewrite /res W_rect_BConsE_subproof; set y := fresh_in _.
set rhs := RHS; set lhs := LHS; rewrite /lhs/rhs.
set a := fresh_in (lhs, rhs, Supp, l, x). 
freshTacCtxt a. freshTacCtxt y.
rewrite -[LHS](@act_fresh _ y a) //; last exact/FCB_fbcons.
rewrite -[RHS](@act_fresh _ x a) //; last exact/FCB_fbcons.
rewrite !f_bcons_equivariant;
  try solve [exact/disjoint_tfsupp]. 
rewrite !tfinpermL.
rewrite -map_equivariant; 
  last by move => ? ?; apply/Hequiv => //; apply/disjoint_tfsupp.
have : y # BinderCons c x l by apply/fresh_repr.
have [/eqP ->|/fresh_atomP zFx /(fresh_BCons zFx) ?] := boolP (y == x).
  by rewrite tfinperm_id !act1.
rewrite ![swap y a\dot _ \dot _]act_conj !tfinpermL !tfinperm_fresh //.
rewrite [swap y a \dot l]act_fresh //.
rewrite [swap y a \dot _]map_id_in // => t /mapP [?] ? ->.
rewrite Hequiv //; last exact/disjoint_tfsupp.
rewrite act_fresh //; by freshTacList.
Qed.

Lemma W_rect_equivariant t :
 equiv t.
Proof.
elim/(@W_ind _ Supp): t => [v|a|c l IHl|c z l zFSupp IHl] π disj_pi_S.
  - by rewrite Var_equivariant !W_rect_VarE f_var_equivariant.
  - by rewrite !Annot_equivariant !W_rect_AnnotE f_annot_equivariant.
  - rewrite !Cons_equivariant !W_rect_ConsE f_cons_equivariant //. 
    rewrite [X in f_cons _ _ X]map_equivariant //; last by
      move => t tl; exact/IHl.
  - have Hres1 := (@equiv_res_subproof c _ _ IHl zFSupp).
    have Hres2 : res c (π z) (π \dot l).
      apply/equiv_res_subproof => //; last exact/disj_im_fresh. 
      move => t /mapP [?] ? -> π' ?.
      rewrite -actM -!IHl // ?actM //; exact/disjoint_conj.
    rewrite BinderCons_equivariant Hres1 Hres2. 
    rewrite f_bcons_equivariant // map_equivariant // => ? ?.
    exact/IHl.
Qed.

Lemma W_rect_BinderConsE c x l : 
  x # Supp -> 
  W_rect (BinderCons c x l) = f_bcons c x l (map W_rect l).
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
Definition subst_annot (a : annot_label ) := Annot a.
Definition subst_cons (c : cons_label) (l : seq W) (subst_l : seq W) :=
  Cons c subst_l.
Definition subst_bcons (c : bcons_label) (y : atom) (l : seq W) (subst_l : seq W) :=
  BinderCons c y subst_l.

Definition subst := 
  @W_rect _ subst_var subst_annot subst_cons subst_bcons Supp dflt.

Lemma subst_var_equiv (π : {finperm atom}) y : 
  [disjoint finsupp π & Supp] -> 
  π \dot subst_var y = subst_var (π y). 
Proof.
rewrite fdisjoint_sym fdisjointU1X => /andP [/finsfun_dflt pix_x disj_pi_Supp].
rewrite /subst_var if_equivariant -{2}pix_x (inj_eq (@finperm_inj _ π)).
by rewrite fresh_perm // Var_equivariant.
Qed.
  
Lemma subst_annot_equiv (π : {finperm atom}) a :
  [disjoint finsupp π & Supp] -> 
  π \dot subst_annot a = subst_annot (π \dot a).
Proof. by rewrite /subst_annot Annot_equivariant. Qed.

Lemma subst_cons_equiv (π : {finperm atom}) c l l' :
    [disjoint finsupp π & Supp] ->
                  π \dot subst_cons c l l' = 
                  subst_cons c (π \dot l) (π \dot l').
Proof. by rewrite /subst_cons Cons_equivariant. Qed.

Lemma subst_bcons_equiv (π : {finperm atom}) c y l l' :
    [disjoint finsupp π & Supp] -> 
    π \dot subst_bcons c y l l' = 
    subst_bcons c (π y) (π \dot l) (π \dot l').    
Proof. by rewrite /subst_bcons BinderCons_equivariant. Qed.

Lemma FCB y c l l' : y # Supp -> y # (subst_bcons c y l l').
Proof. rewrite/subst_bcons => ?. exact/bname_fresh. Qed.

Lemma subst_VarE y : subst (Var y) = if x == y then t else Var y.
Proof. by rewrite /subst W_rect_VarE /subst_var. Qed.

Lemma subst_AnnotE a : subst (Annot a) = Annot a.
Proof. by rewrite /subst W_rect_AnnotE /subst_annot. Qed.

Lemma subst_ConsE c l : subst (Cons c l) = Cons c (map subst l).
Proof. by rewrite /subst W_rect_ConsE /subst_cons. Qed.

Lemma subst_BConsE c y l : 
  y # x -> y # t -> 
  subst (BinderCons c y l) = BinderCons c y (map subst l).
Proof.
move => yFx yFt.
apply W_rect_BinderConsE.
  - exact/subst_var_equiv.
  - exact/subst_annot_equiv.
  - exact/subst_cons_equiv.
  - exact/subst_bcons_equiv.
  - exact/FCB.
(* remplacer Supp -> env *)
Admitted.

End Substitution.

Notation " t { x := u } " := (subst x u t) (at level 0).

End W.