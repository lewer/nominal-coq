From mathcomp
Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq fintype.
From mathcomp
Require Import finfun finset generic_quotient.

Require Import finmap finsfun finperm nominal utilitaires.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope finperm_scope with fperm.
Local Open Scope finperm_scope.
Local Open Scope fset.
Local Open Scope quotient_scope.

Import Key.Exports.

Context (cons_label : eqType)
        (bcons_label : eqType)
        (annot_label : {nominalType atom}).

Section ASTDef.

Inductive rAST :=
|rVar of atom
|rAnnot of annot_label
|rCons of cons_label & seq rAST
|rBinderCons of bcons_label & atom & seq rAST.


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

Lemma rAST_better_ind_subproof (P : rAST -> Prop) (f : seq rAST):
 foldr (fun t => and (P t)) True f -> (forall t, t \in f -> P t).
Proof.
elim: f => [|t l IHl] //=.
move => [Ptt P_all_l] u.
rewrite inE => /orP. case; first by move /eqP ->.
by apply IHl.
Qed.

Definition rAST_better_ind P IH_var IH_annot IH_cons IH_bcons :=
  fix loop t : P t : Prop :=
  let fix iter_conj f : foldr (fun t => and (P t)) True f :=
      if f is t :: f' then conj (loop t) (iter_conj f') else Logic.I
  in
  match t with
    | rVar x => IH_var x
    | rAnnot x => IH_annot x
    | rCons c f0 => IH_cons c f0 (rAST_better_ind_subproof (iter_conj f0))
    | rBinderCons c x f0 => IH_bcons c x f0 (rAST_better_ind_subproof (iter_conj f0))
    end.

Fixpoint rAST_depth (t : rAST) : nat :=
  match t with
    |rVar _ => 0
    |rAnnot _ => 0
    |rCons _ l => (maxlist (map rAST_depth l)).+1
    |rBinderCons _ _ l => (maxlist (map rAST_depth l)).+1
  end.

Fixpoint rAST_act (π : {finperm atom}) (t : rAST) :=
  match t with
    |rVar x => rVar (π x)
    |rAnnot u => rAnnot (π \dot u)
    |rCons c l => rCons c [seq (rAST_act π u) | u <- l]
    |rBinderCons c x l => rBinderCons c (π x) [seq (rAST_act π u) | u <- l]
  end.

Lemma rAST_act1 : rAST_act 1 =1 id.
Proof.
elim/rAST_better_ind => [x|a|c l IHl|c x l IHl] /=.
  - by rewrite finsfun1.
  - by rewrite act1.
  - by rewrite map_id_in //.
  - by rewrite finsfun1 map_id_in.
Qed.

Lemma rAST_actM π π' (t : rAST) :
  rAST_act (π * π') t = rAST_act π (rAST_act π' t).
Proof.
elim/rAST_better_ind :t => [x|a|c l IHl|c x l IHl] /=.
  - by rewrite finsfunM.
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
  @PermSetoidMixin _ rAST (@eq rAST) rAST_act rAST_act1
                   rAST_actM rAST_actproper.

Fixpoint rAST_support t :=
  match t with
    |rVar x => [fset x]
    |rAnnot x => support x
    |rCons _ l => fsetU_list (map rAST_support l)
    |rBinderCons _ x l => x |` (fsetU_list (map rAST_support l))
  end.

Lemma rAST_cons_support (l : seq rAST) (t : rAST) c :
  t \in l -> rAST_support t `<=` rAST_support (rCons c l).
Proof.
move => t_l.
apply/fsubsetP => x x_supp_t.
apply/fsetU_listP. exists (rAST_support t) => //.
exact: map_f.
Qed.

Lemma rAST_bcons_support (l : seq rAST) (t : rAST) c y :
  t \in l -> rAST_support t `<=` rAST_support (rBinderCons c y l).
Proof.
move => t_l.
apply/fsubsetP => x x_supp_t /=.
apply/fset1Ur/fsetU_listP. exists (rAST_support t) => //.
exact: map_f.
Qed.

Lemma rAST_act_id (π : {finperm atom}) (t : rAST) :
     (forall a : atom, a \in rAST_support t -> π a = a) -> rAST_act π t = t.
Proof.
elim/rAST_better_ind : t => [x|a|c l IHl|c x l IHl] Hsupp /=.
  - by rewrite -atomactE act_id.
  - by rewrite act_id.
  - rewrite map_id_in // => t t_in_l.
    apply IHl => // a a_supp_t.
    exact/Hsupp/(fsubsetP (rAST_cons_support c t_in_l) a).
  - rewrite map_id_in.
      by rewrite Hsupp // fset1U1.
    move => t t_in_l.
    apply IHl => // a a_supp_t.
    exact/Hsupp/(fsubsetP (rAST_bcons_support c x t_in_l) a).
Qed.

End ASTDef.

Definition rAST_nominal_mixin  :=
  @NominalMixin _ rAST rAST_nominal_setoid_mixin _
                rAST_act_id.

Canonical rAST_nominalType :=
  NominalType atom rAST rAST_nominal_mixin.

Section rDepth.

Lemma rdepth_cons_leq {c} {l} {n} :
  rAST_depth (rCons c l) <= n.+1 ->
  all (fun t : rAST  => rAST_depth t <= n) l.
Proof.
rewrite ltnS => /maxlist_leqP Hl.
apply/allP => x xl.
exact/Hl/map_f.
Qed.

Lemma rdepth_bcons_leq {c} {l} {n} x :
  rAST_depth (rBinderCons c x l) <= n.+1 ->
  all (fun t : rAST  => rAST_depth t <= n) l.
Proof.
rewrite ltnS => /maxlist_leqP Hl.
apply/allP => t tl.
exact/Hl/map_f.
Qed.

Lemma rdepth_perm (π : {finperm atom}) (t : rAST) :
rAST_depth (π \dot t) = rAST_depth t.
Proof.
elim/rAST_better_ind: t => [x|a|? l ihl|? ? l ihl] //=.
all: apply eq_S; congr maxlist; rewrite -map_comp.
all: apply eq_in_map => t tl /=.
all: exact: ihl.
Qed.

End rDepth.

Section AlphaEquivalence.

Fixpoint alpha_rec (n : nat) (W1 W2 : rAST ) :=
  match n, W1, W2 with
    |_, rVar x, rVar y => x == y
    |_, rAnnot a, rAnnot b => a == b
    |S n, rCons c1 children1, rCons c2 children2 =>
     (c1 == c2) &&
     (all2 (alpha_rec n) children1 children2)
    |S n, rBinderCons c1 x children1, rBinderCons c2 y children2 =>
     (c1 == c2) &&
     (let z := fresh_in (x, children1, y, children2) in
      all2 (alpha_rec n)
           (swap x z \dot children1)
           (swap y z \dot children2))
    |_, _,_ => false
  end.

Definition alpha W1 W2 := alpha_rec (rAST_depth W1) W1 W2.

Lemma alpha_recE n (W1 W2 : rAST) :
  (rAST_depth W1 <= n) ->
  alpha_rec n W1 W2 = alpha W1 W2.
Proof.
rewrite /alpha; move: {-2}n (leqnn n).
elim: n W1 W2 => // [|n ihn] [x|a|c1 l1|c1 x1 l1] [y|b|c2 l2|c2 x2 l2] [|m] //.
  - rewrite ltnS => m_leq_n /rdepth_cons_leq /allP IHl1 /=.
    apply andb_id2l => _.
    apply eq_in_all2 => t1 t2 t1l2 t2l2.
    rewrite !ihn //; last exact: IHl1.
      apply/(@leq_trans m) => //.
      exact/maxlist_map_leqP.
    exact/in_maxlist/map_f.
  - rewrite ltnS => m_leq_n /rdepth_bcons_leq /allP IHl1 /=.
    apply andb_id2l => _.
    apply eq_in_all2 => t1 t2 /mapP [?] ? -> /mapP [?] ? ->.
    rewrite !ihn //; try rewrite rdepth_perm; last exact/IHl1;
      last exact/in_maxlist/map_f.
    apply (@leq_trans m) => //.
    exact/maxlist_map_leqP/IHl1.
Qed.

(* dans la preuve précédente comment éviter la répétition de deux sous-preuves *)
(* identiques ? Il faudrait pouvoir appliquer depth_cons_leq au premier sous but *)
(* et depth_bcons_leq au deuxième *)

Lemma alpha_VarE (x y : atom) :
  alpha (rVar x) (rVar y) = (x == y).
Proof. by rewrite /alpha. Qed.

Lemma alpha_AnnotE (a b : annot_label) :
  alpha (rAnnot a) (rAnnot b) = (a == b).
Proof. by rewrite /alpha. Qed.

Lemma alpha_ConsE (c1 c2 : cons_label) l1 l2 :
  alpha (rCons c1 l1) (rCons c2 l2) = (c1 == c2) && all2 alpha l1 l2.
Proof.
rewrite/alpha /=.
apply andb_id2l => _. apply eq_in_all2 => t1 t2 ? ?.
rewrite alpha_recE //.
exact/in_maxlist/map_f.
Qed.

Lemma alpha_BinderConsE (c1 c2 : bcons_label) x1 x2 l1 l2  :
  alpha (rBinderCons c1 x1 l1) (rBinderCons c2 x2 l2) =
  (c1 == c2) &&
  let z := fresh_in (x1,l1,x2,l2) in
  all2 alpha (swap x1 z \dot l1) (swap x2 z \dot l2).
Proof.
rewrite /alpha /=.
apply andb_id2l => _.
apply eq_in_all2 => t1 t2 /mapP [?] ? -> /mapP [?] ? ->.
rewrite alpha_recE // rdepth_perm.
exact/in_maxlist/map_f.
Qed.

Definition alphaE := (alpha_VarE, alpha_AnnotE, alpha_ConsE, alpha_BinderConsE).

Lemma alpha_equivariant (W1 W2 : rAST ) (π : {finperm atom}):
  alpha (π \dot W1) (π \dot W2) = alpha W1 W2.
Proof.
rewrite/alpha rdepth_perm.
move: {-1}(rAST_depth W1) (leqnn (rAST_depth W1)) => n.
elim: n W1 W2 π => [|n IHn] [x1|a1|c1 l1|c1 x1 l1] [x2|a2|c2 l2|c2 x2 l2] π //=;
  do ?by rewrite inj_eq //; do [apply/finperm_inj|apply/act_inj].
all: rewrite ltnS => /maxlist_map_leqP IHl1.
all: apply andb_id2l => _.
all: rewrite !all2_map; apply eq_in_all2 => t1 t2 ? ?.
  exact/IHn/IHl1.
set z := fresh_in _; set y := fresh_in _.
rewrite -act_conj_imL -[X in alpha_rec _ _ X]act_conj_imL.
rewrite IHn; try rewrite -[RHS](@IHn _ _ (swap y (π^-1 z))).
  all: try (rewrite rdepth_perm; exact: IHl1). (* comment apliquer aux buts 2 et 3 ?) *)
freshTacCtxt z; freshTacCtxt y.
rewrite -{1}[t1](@act_fresh _ y (π^-1 z)) //; try freshTacList;
  last exact: im_inv_fresh.
rewrite -{1}[t2](@act_fresh _ y (π^-1 z)) //; try freshTacList;
  last exact: im_inv_fresh. (* comment réécrire dans t1 et t2 à la fois ? *)
do ?rewrite [swap y _ \dot _  \dot _]act_conj tfinpermL tfinperm_fresh //;
   do?exact/im_inv_fresh.
Qed.

(* Lemma alpha_equivariantR {W1 W2 : rAST} {π1 π2 : {finperm atom}} x y : *)
(*       alpha (π1 \dot W1) (π2 \dot W2) =  *)
(*       alpha (π1 \dot (swap x y) \dot W1) (π2 \dot (swap x y) \dot W2). *)
(* Proof. *)

(*  by rewrite !alpha_equivariant. Qed. *)

Lemma alpha_equivariantprop : equivariant_prop alpha.
Proof. move => π t t' /=. by rewrite alpha_equivariant. Qed.

Lemma alpha_BConsP x1 x2 c1 c2 (l1 l2 : seq rAST) :
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
rewrite all2_map.
eapply iff_stepl. by symmetry; apply new_all2.
eapply iff_stepl. by apply (rwP (@all2P _ _ _ _)).
apply/eq_in_all2_prop => t1 t2 t1l1 t2l2.
apply (@some_fresh_new _ _ Requi _ ((x1, t1), (x2, t2))).
freshTac => *.
apply/fresh_prod; split; apply/fresh_prod;split => //.
all: by freshTacList.
Qed.

Lemma alpha_refl : reflexive alpha.
Proof.
elim/rAST_better_ind => [x|a|c l|c x l]; rewrite alphaE eqxx //= => Hrefl.
all: apply all2_refl => t.
  exact/Hrefl.
move/mapP => [?] ? ->.
rewrite alpha_equivariant. exact/Hrefl.
Qed.

Lemma alpha_sym : symmetric alpha.
Proof.
move => t1 t2; rewrite/alpha.
move: {-1}(rAST_depth t1) (leqnn (rAST_depth t1)) => n.
elim: n t1 t2 => [|n IHn] [x1|a1|c1 l1|c1 x1 l1] [x2|a2|c2 l2|c2 x2 l2] //=;
rewrite eq_sym.
all: rewrite ltnS => /maxlist_map_leqP depth_l1_leqn.
all: apply andb_id2l => _.
2: rewrite !all2_map.
all: apply all2_sym => t1 t2 t1l1 t2l2.
all: rewrite /switch IHn ?rdepth_perm; last by apply depth_l1_leqn.
  exact/sym_eq/alpha_recE/in_maxlist/map_f.
rewrite !alpha_recE; last first.
  by rewrite rdepth_perm.
  rewrite rdepth_perm; exact/in_maxlist/map_f.
suff : fresh_in (x1, l1, x2, l2) = fresh_in (x2, l2, x1, l1) by move ->.
suff : support (x1, l1, x2, l2) = support (x2, l2, x1, l1)
  by rewrite/fresh_in => ->.
repeat (rewrite/support/=).
by rewrite -fsetUA fsetUC fsetUA.
Qed.

Lemma alpha_trans : transitive alpha.
move => t2 t1 t3.
move: {-1}(rAST_depth t1) (leqnn (rAST_depth t1)) => n.
elim: n t1 t2 t3 => [|n IHn] [x1|a1|c1 l1|c1 x1 l1]
                             [x2|a2|c2 l2|c2 x2 l2]
                             [x3|a3|c3 l3|c3 x3 l3] //=;
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
by rewrite rdepth_perm; auto.
Qed.

End AlphaEquivalence.

Section Quotient.

Canonical alpha_equiv :=
  EquivRel alpha alpha_refl alpha_sym alpha_trans.

Definition AST := {eq_quot alpha}.
Definition AST_eqMixin := [eqMixin of AST].
Canonical AST_eqType := EqType AST AST_eqMixin.
Canonical AST_choiceType := Eval hnf in [choiceType of AST].
Canonical AST_countType := Eval hnf in [countType of AST].
Canonical AST_quotType := Eval hnf in [quotType of AST].
Canonical AST_eqQuotType := Eval hnf in
      [eqQuotType alpha of AST].

Lemma alpha_eqE t t' : alpha t t' = (t == t' %[mod AST]).
Proof. by rewrite piE. Qed.

Lemma all2_alpha_eq l1 l2 :
  all2 alpha l1 l2 ->
  map \pi_AST l1 = map \pi_AST l2.
Proof.
move => /all2P alpha_l1l2. apply/all2_prop_eq/all2_prop_map.
move : alpha_l1l2; apply eq_in_all2_prop => t1 t2 t1s1 t2s2.
rewrite alpha_eqE.
by split; move/eqP.
Qed.

Definition Var x := lift_cst AST (rVar x).
Lemma rVarK x : \pi_AST (rVar x) = Var x.
Proof. by unlock Var. Qed.

Definition Annot a := lift_cst AST (rAnnot a).
Lemma rAnnotK a : \pi_AST (rAnnot a) = Annot a.
Proof. by unlock Annot. Qed.

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
rewrite [_ == _]piE alphaE eqxx /=.
rewrite all2_equivariant;
  last by move => ? ? ?; rewrite alpha_equivariant.
rewrite -map_comp all2_mapr. apply all2_refl => t _ /=.
by rewrite alpha_eqE reprK.
Qed.

End Quotient.

Section NominalAST.

Implicit Types (π : {finperm atom}).

Definition AST_act π (t : AST) := \pi_AST (π \dot repr t).

Lemma AST_act1 : AST_act 1 =1 id.
Proof. move => t /=. by rewrite /AST_act act1 reprK. Qed.

Lemma AST_act_equiv π t :
  π \dot (repr t) == repr (AST_act π t) %[mod AST].
Proof. by rewrite /AST_act reprK. Qed.

Lemma AST_actM π π' t : AST_act (π * π') t = AST_act π (AST_act π' t).
Proof.
apply/eqP.
by rewrite /AST_act actM piE alpha_equivariant alpha_eqE reprK.
Qed.

Lemma AST_actproper :
  forall t1 t2 π, t1 = t2 -> (AST_act π t1) = (AST_act π t2).
Proof. by move => t1 t2 π ->. Qed.

Definition AST_nominal_setoid_mixin :=
  @PermSetoidMixin _ AST (@eq AST) AST_act AST_act1 AST_actM AST_actproper.

Lemma AST_act_id π t :
     (forall a : atom, a \in rAST_support (repr t) -> π a = a) ->
     AST_act π t = t.
Proof.
rewrite/AST_act => Hact_id.
by rewrite act_id // reprK.
Qed.

Definition AST_nominal_mixin :=
  @NominalMixin _ AST AST_nominal_setoid_mixin _ AST_act_id.

Canonical AST_nominalType := NominalType atom AST AST_nominal_mixin.

End NominalAST.

Section VariousLemmas.

Lemma pi_equivariant π (t : rAST) :
  π \dot (\pi_AST t) = \pi_AST (π \dot t).
Proof.
apply/eqmodP => /=.
by rewrite alpha_equivariant alpha_eqE reprK.
Qed.

Lemma repr_equivariant π (t : AST) : repr (π \dot t) == π \dot (repr t) %[mod AST].
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

Lemma fresh_repr x (t : AST) : x # (repr t) -> x # t.
Proof.
move => [S [xNS S_supp_t]].
exists S; split => //.
move => π H. by rewrite -[t]reprK pi_equivariant (S_supp_t π) //.
Qed.

Lemma fresh_pi x t : x # t -> x # (\pi_AST t).
Proof.
move => [S [xNS S_supp_t]].
exists S; split => //.
move => π H. by rewrite pi_equivariant (S_supp_t π).
Qed.

Lemma fresh_list_repr x (l : seq AST) : x # (map repr l) -> x # l.
Proof.
move => ?.
apply fresh_list => ? /(map_f (@repr rAST AST_quotType)) ?.
apply fresh_repr; by freshTacList.
Qed.

Lemma fresh_list_pi x l : x # l -> x # (map \pi_AST l).
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

Lemma BConsK c (x : atom) (l : seq AST) : exists (y : atom) (repr_l : seq rAST),
   repr (BinderCons c x l) = rBinderCons c y repr_l.
Proof.
have: alpha (repr (BinderCons c x l)) (rBinderCons c x (map repr l)).
  rewrite alpha_eqE reprK rBinderConsK -map_comp map_id_in //.
  move => t _ /=. by rewrite reprK.
case: (repr (BinderCons _ _ _)) => //= c2 x2 l2.
rewrite alphaE => /andP [/eqP ->] /= H.
by exists x2; exists l2.
Qed.

Lemma AST_caseP (t : AST) :
  (exists x, t = Var x) \/
  (exists x, t = Annot x) \/
  (exists c l, t = Cons c l) \/
  (exists c x l, t = BinderCons c x l).
Proof.
case_eq (repr t) => [x|a|c l|c x l] /(congr1 \pi_AST).
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

Lemma fresh_rBCons x y c (l : seq rAST) :
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
move: tl => /(map_f (@repr rAST AST_quotType)) /= ?.
apply fresh_repr; by freshTacList.
Qed.

Lemma bname_fresh (x : atom) c l : x # (BinderCons c x l).
Proof.
pose y := fresh_in (x, l, BinderCons c x l); freshTacCtxt y.
apply (@CFN_principle y) => //.
rewrite BinderCons_equivariant tfinpermL.
exact/sym_eq/eq_BCons.
Qed.

End VariousLemmas.

Section Depth.

Definition depth (t : AST) := rAST_depth (repr t).

Lemma rdepth_alpha t u : alpha t u -> rAST_depth t = rAST_depth u.
Proof.
elim/rAST_better_ind: t u => [x1|a1|c1 l1 IHl1|c1 x1 l1 IHl1] [x2|a2|c2 l2|c2 x2 l2] //=.
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

Lemma depth_rdepth t : depth (\pi t) = rAST_depth t.
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

Lemma AST_naive_ind (P : AST -> Prop) :
  (forall x, P (Var x)) ->
  (forall x, P (Annot x)) ->
  (forall c l, (forall t, t \in l -> P t) -> P (Cons c l)) ->
  (forall c x l, (forall t, t \in l -> P t) -> P (BinderCons c x l)) ->
  forall u, P u.
(* {in l, P} ? *)
Proof.
move => HVar HAnnot HCons HBCons u; rewrite -[u]reprK.
elim/rAST_better_ind : (repr u) => [x|a|c l IHl|c x l IHl] /=.
  - by rewrite rVarK.
  - by rewrite rAnnotK.
  - rewrite rConsK. apply HCons => t /mapP [reprt ?] ->.
    exact/IHl.
  - rewrite rBinderConsK. apply HBCons => t /mapP [reprt ?] ->.
    exact/IHl.
Qed.

Lemma AST_ind {env : {nominalType atom}} (C : env) (P : AST -> Prop) :
  (forall x, P (Var x)) ->
  (forall x, P (Annot x)) ->
  (forall c l, (forall t, t \in l -> P t) -> P (Cons c l)) ->
  (forall c x l, x # C -> (forall t, t \in l -> P t) -> P (BinderCons c x l)) ->
  forall u, P u.
(* {in l, P} ? *)
Proof.
move => HVar HAnnot HCons HBcons u.
suff : forall π, P (π \dot u).
  by move => /(_ 1); rewrite act1.
elim/AST_naive_ind : u => [x|a|c l IHl|c x l IHl] π.
  - by rewrite Var_equivariant.
  - by rewrite Annot_equivariant.
  - rewrite Cons_equivariant. apply HCons => t /mapP [reprt ?] ->.
    exact/IHl.
  - rewrite BinderCons_equivariant.
    pose z := fresh_in (C, π \dot x, π \dot l); freshTacCtxt z.
    rewrite (@eq_BCons _ _ z) -?actM => //.
    apply HBcons => // t /mapP [reprt ?] ->.
    exact/IHl.
Qed.

Variables (X : {nominalType atom})
          (f_var : atom -> X)
          (f_annot : annot_label -> X)
          (f_cons : cons_label -> seq AST -> seq X -> X)
          (f_bcons : bcons_label -> atom -> seq AST -> seq X -> X)
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


Fixpoint AST_rect_rec (n : nat) (t : AST):=
  match n, (repr t) with
    |_, rVar x => f_var x
    |_, rAnnot x => f_annot x
    |S n, rCons c l => f_cons c (map \pi l) (map (AST_rect_rec n) (map \pi l))
    |S n, rBinderCons c x l =>
     let z := fresh_in (Supp, rBinderCons c x l) in
     f_bcons c z
             (swap x z \dot (map \pi_AST l))
             (map (AST_rect_rec n) (swap x z \dot map \pi_AST l))
    |_, _ => dflt
  end.

Definition AST_rect t := AST_rect_rec (depth t) t.

Lemma AST_rect_recE n t : depth t <= n -> AST_rect_rec n t = AST_rect t.
Proof.
rewrite/AST_rect; move: {-2}n (leqnn n).
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

Lemma AST_rect_VarE x : AST_rect (Var x) = f_var x.
Proof. by rewrite /AST_rect depth_Var /= VarK. Qed.

Lemma AST_rect_AnnotE x : AST_rect (Annot x) = f_annot x.
Proof. by rewrite /AST_rect depth_Annot /= AnnotK. Qed.

Lemma AST_rect_ConsE c l :
  AST_rect (Cons c l) = f_cons c l (map AST_rect l).
Proof.
rewrite/AST_rect depth_Cons /=.
have [reprl [-> ->]] := ConsK c l.
congr f_cons => //.
rewrite -!map_comp. apply eq_in_map => t /= ?.
apply AST_rect_recE => /=.
exact/in_maxlist/map_f.
Qed.

Lemma AST_rect_BConsE_subproof c x l :
  let z := (fresh_in (Supp, repr (BinderCons c x l))) in
    AST_rect (BinderCons c x l) =
    f_bcons c z (swap x z \dot l) (map AST_rect (swap x z \dot l)).
have [y [l'] repr_cxl] := BConsK c x l => /=.
rewrite /AST_rect depth_BinderCons /= repr_cxl.
set z := fresh_in _.
suff : swap y z \dot (map \pi_AST l') = swap x z \dot l.
  move => ->. congr f_bcons.
  apply eq_in_map => ? /mapP [?] ? ->.
  rewrite AST_rect_recE // depth_perm. exact/in_maxlist/map_f.
move: (congr1 \pi_AST repr_cxl).
rewrite reprK rBinderConsK => /eq_BConsE /(_ z) H.
have : z # (rBinderCons c y l') by freshTac.
move => /fresh_rBCons [? /fresh_list_pi ?].
have [/eqP z_eq_x|/fresh_atomP ?] := boolP (z == x).
  rewrite z_eq_x tfinperm_id act1.
  move: (congr1 \pi_AST repr_cxl); rewrite reprK rBinderConsK.
  rewrite [X in _ = X](@eq_BCons c y x) -?z_eq_x // => J.
  exact/BConsx_inj/sym_eq/J.
apply H => //. apply/(@fresh_BCons _ x c) => //.
apply fresh_repr; rewrite repr_cxl.
by freshTac.
Qed.

Definition equiv t :=
  forall (π : {finperm atom}), [disjoint finsupp π & Supp] ->
                               π \dot (AST_rect t) =
                               AST_rect (π \dot t).

Definition res c x l := AST_rect (BinderCons c x l) =
                        f_bcons c x l (map AST_rect l).

Lemma equiv_res_subproof c (x : atom) (l : seq AST) :
(forall (t : AST), t \in l -> equiv t) ->
x # Supp -> res c x l.
Proof.
move => Hequiv zFSupp.
rewrite /res AST_rect_BConsE_subproof; set y := fresh_in _.
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

Lemma AST_rect_equivariant t :
 equiv t.
Proof.
elim/(@AST_ind _ Supp): t => [v|a|c l IHl|c z l zFSupp IHl] π disj_pi_S.
  - by rewrite Var_equivariant !AST_rect_VarE f_var_equivariant.
  - by rewrite !Annot_equivariant !AST_rect_AnnotE f_annot_equivariant.
  - rewrite !Cons_equivariant !AST_rect_ConsE f_cons_equivariant //.
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

Lemma AST_rect_BinderConsE c x l :
  x # Supp ->
  AST_rect (BinderCons c x l) = f_bcons c x l (map AST_rect l).
Proof.
move => xFsupp.
apply/equiv_res_subproof => // ? ?.
exact/AST_rect_equivariant.
Qed.

End EliminationPrinciples.
