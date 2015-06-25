From Ssreflect
Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq fintype.
From MathComp
Require Import finfun finset generic_quotient.
From Nominal
Require Import finmap finsfun finperm nominal utilitaires.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope finperm_scope with fperm.
Local Open Scope finperm_scope.
Local Open Scope fset.
Local Open Scope quotient_scope.

Import Key.Exports.

Section ASTDef.

Variables (node_label : Type) (leaf_type: nominalType atom).

Inductive rAST := 
|rLeaf of leaf_type
|rCons of node_label & seq rAST
|rBinderCons of node_label & atom & seq rAST.


(* TODO : encodage des rAST *)
Definition rAST_encode : rAST -> GenTree.tree atom. Admitted.
Definition rAST_decode : GenTree.tree atom -> rAST. Admitted.
Lemma rAST_codeK : cancel rAST_encode rAST_decode. Admitted.

Definition rAST_eqMixin := CanEqMixin rAST_codeK.
Canonical rAST_eqType := EqType rAST rAST_eqMixin.
Definition rAST_choiceMixin := CanChoiceMixin rAST_codeK.
Canonical rAST_choiceType := ChoiceType rAST rAST_choiceMixin.
Definition rAST_countMixin := CanCountMixin rAST_codeK.
Canonical rAST_countType := CountType rAST rAST_countMixin.

Definition rAST_better_rect T IH_leaf IH_cons IH_bcons :=
  fix loop t : T  := 
  let fix result_list f : seq T :=
      if f is t :: f' then loop t :: (result_list f') else nil
  in
  match t with
  | rLeaf x => IH_leaf x
  | rCons c f0 => IH_cons c f0 (result_list f0)
  | rBinderCons c x f0 => IH_bcons (c,x) f0 (result_list f0) 
    end.

Lemma rAST_better_ind_subproof (P : rAST -> Prop) (f : seq rAST): 
 foldr (fun t => and (P t)) True f -> (forall t, t \in f -> P t).
Proof.
elim: f => [|t l IHl] //=. 
move => [Ptt P_all_l] u. 
rewrite inE => /orP. case; first by move /eqP ->.
by apply IHl.
Qed.

Definition rAST_better_ind P IH_leaf IH_cons IH_bcons :=
  fix loop t : P t : Prop := 
  let fix iter_conj f : foldr (fun t => and (P t)) True f :=
      if f is t :: f' then conj (loop t) (iter_conj f') else Logic.I
  in
  match t with
  | rLeaf x => IH_leaf x
  | rCons c f0 => IH_cons c f0 (rAST_better_ind_subproof (iter_conj f0))
  | rBinderCons c x f0 => IH_bcons c x f0 (rAST_better_ind_subproof (iter_conj f0))
    end.

Variable (s : seq nat).

Fixpoint rAST_depth (t : rAST) : nat :=
  match t with
    |rLeaf _ => 0
    |rCons _ l => (maxlist (map rAST_depth l)).+1
    |rBinderCons _ _ l => (maxlist (map rAST_depth l)).+1
  end.

Fixpoint rAST_act (π : {finperm atom}) (t : rAST) :=
  match t with
    |rLeaf u => rLeaf (π \dot u)
    |rCons c l => rCons c [seq (rAST_act π u) | u <- l]
    |rBinderCons c x l => rBinderCons c (π x) [seq (rAST_act π u) | u <- l]
  end.

Lemma rAST_act1 : rAST_act (1 atom) =1 id.
Proof. 
elim/rAST_better_ind => [x|c l IHl|c x l IHl] /=.
  - by rewrite act1.
  - by rewrite map_id_in //.
  - by rewrite finsfun1 map_id_in.
Qed.

Lemma rAST_actM π π' (t : rAST) : 
  rAST_act (π * π') t = rAST_act π (rAST_act π' t).
Proof.
elim/rAST_better_ind :t => [x|c l IHl|c x l IHl] /=.
  - by rewrite actM.
  - congr rCons. rewrite -map_comp. 
    apply eq_in_map => t /=. exact: IHl.
  - congr rBinderCons. 
      by rewrite finsfunM.
    rewrite -map_comp. apply eq_in_map => t /=.
    exact: IHl.
Qed.

Lemma rAST_actproper : forall t1 t2 π, t1 = t2 -> (rAST_act π t1) = (rAST_act π t2).
Proof. by move => t1 t2 π ->. Qed.

Definition rAST_nominal_setoid_mixin := 
  @PermSetoidMixin rAST (@eq rAST) atom rAST_act rAST_act1 
                   rAST_actM rAST_actproper.   

Definition rAST_support : rAST -> {fset atom}.
apply/rAST_better_rect => [leaf|_ _ children_supports|[_ x] _ children_supports].
  - exact: support leaf.
  - exact: (fsetU_list children_supports).
  - exact: (x |` (fsetU_list children_supports)).
Defined.

Lemma rAST_cons_support (l : seq rAST) (t : rAST) c :
  t \in l -> rAST_support t `<=` rAST_support (rCons c l).
Proof.
move => t_l. 
apply/fsubsetP => x x_supp_t.
apply/fsetU_listP. exists (rAST_support t) => //.
exact: map_f.
Qed.

Lemma rAST_act_id (π : {finperm atom}) (t : rAST) :
     (forall a : atom, a \in rAST_support t -> π a = a) -> rAST_act π t = t.
Proof.
elim/rAST_better_ind : t => [x|c l IHl|c x l IHl] Hsupp /=.
  - by rewrite act_id.
  - rewrite map_id_in // => t t_in_l.
    apply IHl => // a a_supp_t.
    exact/Hsupp/(fsubsetP (rAST_cons_support c t_in_l) a). 
  - rewrite map_id_in.
      by rewrite Hsupp // fset1U1. 
    move => t t_in_l.
    apply IHl => // a a_supp_t.
    exact/Hsupp/fset1Ur/(fsubsetP (rAST_cons_support c t_in_l) a).
Qed.

End ASTDef.

Definition rAST_nominal_mixin (node_label : Type) (leaf_type : nominalType atom) :=
  @NominalMixin (rAST_choiceType node_label leaf_type) atom 
                (rAST_nominal_setoid_mixin node_label leaf_type) _ 
                (@rAST_act_id node_label leaf_type).

Canonical rAST_nominalType (node_label : Type) (leaf_type : nominalType atom) := 
  @NominalType atom
    (@rAST_choiceType node_label leaf_type) 
    (@rAST_nominal_mixin node_label leaf_type).

Section Depth.

Variables (node_label : Type) (leaf_type : nominalType atom).
  
Lemma depth_cons_leq {c} {l} {n} : 
  rAST_depth (rCons c l) <= n.+1 -> 
  all (fun t : rAST node_label leaf_type => rAST_depth t <= n) l.
Proof.
rewrite ltnS => /maxlist_leqP Hl.
apply/allP => x xl. 
exact/Hl/map_f.
Qed.

Lemma depth_perm (π : {finperm atom}) (t : rAST node_label leaf_type) : 
rAST_depth (π \dot t) = rAST_depth t.
Proof. 
elim/rAST_better_ind: t => [x|? l ihl|? ? l ihl] //=. 
all: apply eq_S; congr maxlist; rewrite -map_comp.
all: apply eq_in_map => t tl /=.
all: exact: ihl.
Qed.

End Depth.

Section WellFormedness.

Variables (node_label : Type) (leaf_type : nominalType atom) (arity : node_label -> nat).

Fixpoint wf (t : rAST node_label leaf_type) : bool :=
  match t with
    |rLeaf _ => true
    |rCons c l => (size l == arity c) && (all wf l)
    |rBinderCons c _ l => (size l == arity c) && (all wf l)
  end.

Definition wf_rAST := sig_subType wf.

End WellFormedness.

Section AlphaEquivalence.

Variables (node_label : eqType) 
          (leaf_type : nominalType atom) 
          (arity : node_label -> nat).

Fixpoint alpha_rec (n : nat) (W1 W2 : rAST node_label leaf_type) :=
  match n, W1, W2 with
    |_, rLeaf x, rLeaf y => x == y
    |S n, rCons c1 children1, rCons c2 children2 => 
     (c1 == c2) && 
     (all2 (alpha_rec n) children1 children2)
    |S n, rBinderCons c1 x children1, rBinderCons c2 y children2 =>
     (c1 == c2) && 
     (let z := fresh_in (x, children1, y, children2) in
                    all2
                      (fun w1 w2 => alpha_rec n (swap x z \dot w1) (swap y z \dot w2))
                      children1
                      children2)
    |_, _,_ => false
  end.

Definition alpha W1 W2 := alpha_rec (rAST_depth W1) W1 W2.     

Lemma alpha_recE n (W1 W2 : rAST node_label leaf_type ) : 
  (rAST_depth W1 <= n) -> 
  alpha_rec n W1 W2 = alpha W1 W2.
Proof.
rewrite /alpha; move: {-2}n (leqnn n).
elim: n W1 W2 => // [|n ihn] [x|c1 l1|c1 x1 l1] [y|c2 l2|c2 x2 l2] [|m] //.
all: rewrite ltnS => m_leq_n /(@depth_cons_leq _ _ _) /allP IHl1 /=.  
all: apply andb_id2l => _. 
all: apply eq_in_all2 => t1 t2 t1l2 t2l2.
  - rewrite !ihn //; last exact: IHl1.
      apply/(@leq_trans m) => //. 
      exact/maxlist_map_leqP.
    exact/in_maxlist/map_f.
  - rewrite !ihn //; last rewrite depth_perm; last exact: IHl1.
      apply (@leq_trans m) => //. 
      exact/maxlist_map_leqP/IHl1.
  rewrite depth_perm. exact/in_maxlist/map_f.
Qed.

Lemma alpha_LeafE (x y : leaf_type) : 
  alpha (rLeaf node_label x) (rLeaf node_label y) = (x == y).
Proof. by rewrite /alpha. Qed.

Lemma alpha_ConsE (c1 c2 : node_label) l1 l2 : 
  alpha (rCons c1 l1) (rCons c2 l2) = (c1 == c2) && all2 alpha l1 l2.
Proof. 
rewrite/alpha /=. 
apply andb_id2l => _. apply eq_in_all2 => t1 t2 ? ?.
rewrite alpha_recE //. 
exact/in_maxlist/map_f.
Qed.

Lemma alpha_BinderConsE (c1 c2 : node_label) x1 x2 l1 l2  : 
  alpha (rBinderCons c1 x1 l1) (rBinderCons c2 x2 l2) = 
  (c1 == c2) &&
  let z := fresh_in (x1,l1,x2,l2) in
  all2 (fun w1 w2 => alpha (swap x1 z \dot w1) (swap x2 z \dot w2)) l1 l2.
Proof. 
rewrite /alpha /=. 
apply andb_id2l => _. apply eq_in_all2 => t1 t2 ? ?.
rewrite alpha_recE // depth_perm.
exact/in_maxlist/map_f.
Qed.

Definition alphaE := (alpha_LeafE, alpha_ConsE, alpha_BinderConsE).

Lemma alpha_equivariant (W1 W2 : rAST node_label leaf_type) (π : {finperm atom}):
  alpha (π \dot W1) (π \dot W2) = alpha W1 W2.
Proof.
rewrite/alpha depth_perm.
move: {-1}(rAST_depth W1) (leqnn (rAST_depth W1)) => n.
elim: n W1 W2 π => [|n IHn] [x1|c1 l1|c1 x1 l1] [x2|c2 l2|c2 x2 l2] π //=.
  rewrite inj_eq //. exact: act_inj.
  rewrite inj_eq //. exact: act_inj.
  (* comment appliquer aux deux sous-buts sans recopier ? *)
all: rewrite ltnS => /maxlist_map_leqP IHl1.
all: apply andb_id2l => _.
all: rewrite all2_map; apply eq_in_all2 => t1 t2 t1l1 t2l2.
  exact/IHn/IHl1.
set z := fresh_in _; set y := fresh_in _.
rewrite -act_conj_imL -[X in alpha_rec _ _ X]act_conj_imL.
rewrite IHn; try rewrite -[RHS](@IHn _ _ (swap y (π^-1 z))).
  all: try (rewrite depth_perm; exact: IHl1). (* comment apliquer aux buts 2 et 3 ?) *)
freshTacCtxt z; freshTacCtxt y.
rewrite -{1}[t1](@fresh_transp _ y (π^-1 z)) //; try freshTacList;
  last exact: im_inv_fresh.
rewrite -{1}[t2](@fresh_transp _ y (π^-1 z)) //; try freshTacList;
  last exact: im_inv_fresh. (* comment réécrire dans t1 et t2 à la fois ? *)
rewrite 2?[in RHS]act_conj tfinpermL !tfinperm_fresh //.
all: exact/im_inv_fresh. 
Qed.

Lemma alpha_equivariantprop : equivariant_prop alpha.
Proof. move => π t t' /=. by rewrite alpha_equivariant. Qed.

Lemma alpha_BConsP x1 x2 c1 c2 (l1 l2 : seq (@rAST node_label leaf_type)) : 
  reflect (c1 = c2 /\
           \new z, (all2 (fun t1 t2 => alpha (swap x1 z \dot t1)
                                            (swap x2 z \dot t2))
                                            l1 l2))
          (alpha (rBinderCons c1 x1 l1) (rBinderCons c2 x2 l2)).
Proof.
move : (equi_funprop (@swap_equiv _) alpha_equivariantprop) => /= Requi.
rewrite alphaE.
apply/(equivP andP); apply and_iff_congr => /=.
  by symmetry; apply (rwP eqP).
eapply iff_stepl. by symmetry; apply new_all2.
eapply iff_stepl. by apply (rwP (@all2P _ _ _ _)). (* comment faire plus élégant ?*)
apply eq_in_all2_prop => t1 t2 t1l1 t2l2.
apply (@some_fresh_new _ _ Requi _ ((x1, t1), (x2, t2))).
freshTac => *.
apply/fresh_prod; split; apply/fresh_prod;split => //.
all: by freshTacList.
Qed.

Lemma alpha_refl : reflexive alpha.
Proof.
elim/rAST_better_ind => [s|c l|c x l]; rewrite alphaE eqxx //= => Hrefl.
all: apply all2_refl => t.
  exact/Hrefl.
rewrite alpha_equivariant. exact/Hrefl.
Qed.

Lemma alpha_sym : symmetric alpha.
Proof.
move => t1 t2; rewrite/alpha.
move: {-1}(rAST_depth t1) (leqnn (rAST_depth t1)) => n.
elim: n t1 t2 => [|n IHn] [x1|c1 l1|c1 x1 l1] [x2|c2 l2|c2 x2 l2] //=;
rewrite eq_sym.
all: rewrite ltnS => /maxlist_map_leqP depth_l1_leqn.
all: apply andb_id2l => _.
all: apply all2_sym => t1 t2 t1l1 t2l2.
all: rewrite /switch IHn ?depth_perm; last by apply depth_l1_leqn.
  exact/sym_eq/alpha_recE/in_maxlist/map_f.
rewrite !alpha_recE; last first.
  by rewrite depth_perm. 
  rewrite depth_perm; exact/in_maxlist/map_f.
suff : fresh_in (x1, l1, x2, l2) = fresh_in (x2, l2, x1, l1) by move ->.
suff : support (x1, l1, x2, l2) = support (x2, l2, x1, l1) 
  by rewrite/fresh_in => ->. 
repeat (rewrite/support/=).
by rewrite -fsetUA fsetUC fsetUA. 
Qed.

Lemma alpha_trans : transitive alpha.
move => t2 t1 t3.
move: {-1}(rAST_depth t1) (leqnn (rAST_depth t1)) => n.
elim: n t1 t2 t3 => [|n IHn] [x1|c1 l1|c1 x1 l1] 
                             [x2|c2 l2|c2 x2 l2] 
                             [x3|c3 l3|c3 x3 l3] //=; 
try solve [move => _; apply eq_op_trans].
all: rewrite ltnS => /maxlist_map_leqP deptht1_leqn.
  rewrite !alphaE => /andP [c1_eq_c2 Hl1l2] /andP [c2_eq_c3 Hl2l3].
  rewrite (eq_op_trans c1_eq_c2 c2_eq_c3) /=.
  move: Hl1l2 Hl2l3; apply all2_trans => t1 t2 t3 t1l1 t2l2 t3l3.
  by apply/IHn; auto.
move => /alpha_BConsP [c1_eq_c2 /new_all2 alpha_l1l2].
move => /alpha_BConsP [c2_eq_c3 /new_all2 alpha_l2l3].
apply/alpha_BConsP; split; first exact: eq_trans c1_eq_c2 c2_eq_c3.
apply/new_all2. move: alpha_l1l2 alpha_l2l3.
apply all2_prop_trans => t1 t2 t3 t1l1 t2l2 t3l3 [St1t2] HSt1t2 [St2t3] HSt2t3.
exists (St1t2 `|` St2t3) => a aFSt1t2St2t3.
move: (HSt1t2 _ (fresh_fsetU1 aFSt1t2St2t3)) (HSt2t3 _ (fresh_fsetU2 aFSt1t2St2t3)).
apply IHn.
by rewrite depth_perm; auto.
Qed.

End AlphaEquivalence.

Section Quotient.

Variables (node_label : eqType) (leaf_type : nominalType atom).

Canonical alpha_equiv := 
  EquivRel (@alpha node_label leaf_type) 
           (@alpha_refl node_label leaf_type) 
           (@alpha_sym node_label leaf_type) 
           (@alpha_trans node_label leaf_type).

Definition AST := {eq_quot @alpha node_label leaf_type}.
Definition AST_eqMixin := [eqMixin of AST].
Canonical AST_eqType := EqType AST AST_eqMixin.
Canonical AST_choiceType := Eval hnf in [choiceType of AST].
Canonical AST_countType := Eval hnf in [countType of AST].
Canonical AST_quotType := Eval hnf in [quotType of AST].
Canonical AST_eqQuotType := Eval hnf in 
      [eqQuotType (@alpha node_label leaf_type) of AST].

Lemma alpha_eqE t t' : alpha t t' = (t == t' %[mod AST]).
Proof. by rewrite piE. Qed.

Lemma all2_alpha_eq l1 l2 : 
  all2 (@alpha node_label leaf_type) l1 l2 -> 
  map \pi_AST l1 = map \pi_AST l2. 
Proof.
move => /all2P alpha_l1l2. apply/all2_prop_eq/all2_prop_map.
move : alpha_l1l2; apply eq_in_all2_prop => t1 t2 t1s1 t2s2.
rewrite alpha_eqE. 
by split; move/eqP.
Qed.

Definition Leaf x := lift_cst AST (rLeaf node_label x).
Lemma rLeafK x : \pi_AST (rLeaf node_label x) = Leaf x.
Proof. by unlock Leaf. Qed.

Notation lift_map f := 
  (locked (fun l : seq AST => \pi_AST (f (map (@repr _ AST_quotType) l)))).

Definition Cons c := lift_map (rCons c).
Lemma rConsK c l : \pi_AST (rCons c l) = Cons c (map \pi_AST l).
Proof.
unlock Cons; apply/eqP. 
rewrite [_ == _]piE alphaE eqxx /= -map_comp.
rewrite all2_mapr. apply all2_refl => t _ /=.
by rewrite alpha_eqE reprK.
Qed.

Definition BinderCons c x := lift_map (rBinderCons c x).
Lemma rBinderConsK c x l : \pi_AST (rBinderCons c x l) = BinderCons c x (map \pi_AST l).
Proof.
unlock BinderCons; apply/eqP.
rewrite [_ == _]piE alphaE eqxx /= -map_comp.
rewrite all2_mapr. apply all2_refl => t _ /=.
by rewrite alpha_equivariant alpha_eqE reprK.
Qed.

Lemma LeafK x : repr (Leaf x) = rLeaf node_label x. 
Proof.
have : alpha (repr (Leaf x)) (rLeaf node_label x). 
(* comment ne pas avoir à spécifier node_lavel ? *)
  by rewrite alpha_eqE reprK rLeafK. 
by case: (repr (Leaf x)) => // ? /eqP ->. 
Qed.

Lemma ConsK c l : exists repr_l,
    l = map \pi_AST repr_l /\ repr (Cons c l) = rCons c repr_l.
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

Lemma Leaf_inj x y : Leaf x = Leaf y -> x = y.
Proof. move/(congr1 repr). rewrite !LeafK => H. by injection H. Qed.

Lemma Cons_inj c1 c2 l1 l2 : 
  Cons c1 l1 = Cons c2 l2 -> c1 = c2 /\ l1 = l2.
Proof.
move/(congr1 repr). 
have [reprl1 [-> ->]] := ConsK c1 l1.
have [reprl2 [-> ->]] := ConsK c2 l2.
move => H.
by injection H => -> ->. 
Qed.

End Quotient.


Record AST_Instance := 
  ASTInstance {
      X : Type;
      node_label : Type;
      leaf_type : nominalType atom;
      encode : X -> rAST node_label leaf_type;
      decode : rAST node_label leaf_type -> X;
      _ : cancel encode decode
}.