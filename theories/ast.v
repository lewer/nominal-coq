From Ssreflect
Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq fintype.
From MathComp
Require Import bigop  finfun finset generic_quotient perm tuple fingroup.
From Nominal
Require Import finmap finsfun finperm nominal ast.

Require Import Program.

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
|rBinderCons of node_label * atom & seq rAST.


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
  | rBinderCons (c, x) f0 => IH_bcons (c,x) f0 (result_list f0) 
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
  | rBinderCons (c, x) f0 => IH_bcons (c,x) f0 (rAST_better_ind_subproof (iter_conj f0))
    end.

Definition rAST_depth : rAST -> nat.
apply/rAST_better_rect => [_|_ _ l|_ _ l].
  - exact: 0. 
  - exact: (foldr maxn 0 l).+1.
  - exact: (foldr maxn 0 l).+1.
Defined.

Fixpoint rAST_act (π : {finperm atom}) (t : rAST) :=
  match t with
    |rLeaf u => rLeaf (π \dot u)
    |rCons c l => rCons c [seq (rAST_act π u) | u <- l]
    |rBinderCons (c, x) l => rBinderCons (c, π x) [seq (rAST_act π u) | u <- l]
  end.

Lemma rAST_act1 : rAST_act (1 atom) =1 id.
Proof. 
elim/rAST_better_ind => [x|c l IHl|[c x] l IHl] /=.
  - by rewrite act1.
  - by rewrite map_id_in //.
  - by rewrite finsfun1 map_id_in.
Qed.

Lemma rAST_actM π π' (t : rAST) : 
  rAST_act (π * π') t = rAST_act π (rAST_act π' t).
Proof.
elim/rAST_better_ind :t => [x|c l IHl|[c x] l IHl] /=.
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
elim/rAST_better_ind : t => [x|c l IHl|[c x] l IHl] Hsupp /=.
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

Section AlphaEquivalence.

Variables (node_label : eqType) (leaf_type : nominalType atom).

Fixpoint alpha_rec (n : nat) (W1 W2 : rAST node_label leaf_type) :=
  match n, W1, W2 with
    |_, rLeaf x, rLeaf y => x == y
    |S n, rCons c1 children1, rCons c2 children2 => 
     (c1 == c2) && (all (fun z => alpha_rec n z.1 z.2) (zip children1 children2))
    |S n, rBinderCons (c1, x) children1, rBinderCons (c2, y) children2 =>
     (c1 == c2) && (let z := fresh_in (x, children1, y, children2) in
                    all 
                      (fun w => alpha_rec n (swap x z \dot w.1) (swap y z \dot w.2))
                      (zip children1 children2))
    |_, _,_ => false
  end.

Definition alpha W1 W2 := alpha_rec (rAST_depth W1) W1 W2.     

End AlphaEquivalence.


Record AST_Instance := 
  ASTInstance {
      X : Type;
      node_label : Type;
      leaf_type : nominalType atom;
      encode : X -> rAST node_label leaf_type;
      decode : rAST node_label leaf_type -> X;
      _ : cancel encode decode
}.