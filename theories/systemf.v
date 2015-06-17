From Ssreflect
Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq fintype.
From MathComp
Require Import bigop  finfun finset generic_quotient perm tuple fingroup.
From Nominal
Require Import finmap finsfun finperm nominal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope finperm_scope with fperm.
Local Open Scope finperm_scope.
Local Open Scope fset.
Local Open Scope quotient_scope.

Import Key.Exports.

Section SystemF.

Definition kind := nat.
Definition type_atom := atom.
Definition term_atom := atom.

Section NominalRawtype.

Inductive rawtype : Type :=
| rTVar of type_atom
| rTArrow of rawtype & rawtype
| rTAll of type_atom & kind & rawtype.

Fixpoint rawtypeact (π : {finperm atom}) T :=
  match T with
    | rTVar X => rTVar (π X)
    | rTArrow T1 T2 => rTArrow (rawtypeact π T1) (rawtypeact π T2)
    | rTAll X k T => rTAll (π X) k (rawtypeact π T)
  end.

Fixpoint rawtype_support T :=
  match T with
    |rTVar X => [fset X]
    |rTArrow T1 T2 => rawtype_support T1 `|` rawtype_support T2
    |rTAll X k T => X |` rawtype_support T
  end.

(* Fixpoint type_encode (T : type) : GenTree.tree (atom * kind) := *)
(*   match T with *)
(*     | TVar X => GenTree.Leaf (X, 0) *)
(*     | TArrow T1 T2 => GenTree.Node (0, 0) [:: type_encode T1 :: type_encode T2] *)
(*     | TAll (X, k) T => GenTree.Node (X.+1, k) [:: type_encode T] *)
(*   end. *)

(* Fixpoint rawterm_decode (t : GenTree.tree nat) : rawterm := *)
(*   match t with *)
(*     | GenTree.Leaf a => rVar a *)
(*     | GenTree.Node a.+1 [:: u] => rLambda a (rawterm_decode u) *)
(*     | GenTree.Node 0 [:: u; v] => *)
(*       rApp (rawterm_decode u) (rawterm_decode v) *)
(*     | _ =>rVar 0 *)
(*   end. *)

Definition rawtype_encode : rawtype -> GenTree.tree atom. Admitted.
Definition rawtype_decode : GenTree.tree atom -> rawtype. Admitted.

Lemma rawtype_codeK : cancel rawtype_encode rawtype_decode.
Proof. Admitted. 

Definition rawtype_eqMixin := CanEqMixin rawtype_codeK.
Canonical rawtype_eqType := EqType rawtype rawtype_eqMixin.
Definition rawtype_choiceMixin := CanChoiceMixin rawtype_codeK.
Canonical rawtype_choiceType := ChoiceType rawtype rawtype_choiceMixin.
Definition rawtype_countMixin := CanCountMixin rawtype_codeK.
Canonical rawtype_countType := CountType rawtype rawtype_countMixin.

Lemma rawtypeact1 : rawtypeact (1 atom) =1 id.
Proof.
elim => [X|T1 IHT1 T2 IHT2| X k T IHT];
by rewrite /= ?finsfun1 ?IHT1 ?IHT2 ?IHT.
Qed.

Lemma rawtypeactM π π' T : rawtypeact (π * π') T = rawtypeact π (rawtypeact π' T).
Proof.
elim: T => [X|T1 IHT1 T2 IHT2|X k T IHT];
by rewrite /= ?finsfunM ?IHT1 ?IHT2 ?IHT.   
Qed.

Lemma rawtypeactproper : forall T1 T2 π, T1 = T2 -> (rawtypeact π T1) = (rawtypeact π T2).
Proof. by move => t1 t2 π ->. Qed.

Definition rawtype_nominal_setoid_mixin := 
  @PermSetoidMixin rawtype (@eq rawtype) atom rawtypeact rawtypeact1 
                   rawtypeactM rawtypeactproper.   

Lemma rawtypeact_id (π : {finperm atom}) T :
     (forall a : atom, a \in rawtype_support T -> π a = a) -> rawtypeact π T = T.
Proof.
elim: T => [X |T1 IHT1 T2 IHT2|X k T IHT] /= Hsupp.
  - rewrite  Hsupp //. by rewrite in_fset1.
  - rewrite IHT1 ?IHT2 // => a a_supp_T;
    rewrite ?Hsupp // in_fsetU a_supp_T ?orbT //.
  - rewrite IHT ?Hsupp // ?fset1U1 // => b bsuppt. by apply/Hsupp/fset1Ur.
Qed.

End NominalRawtype.

Definition rawtype_nominal_mixin :=
  @NominalMixin rawtype_choiceType atom rawtype_nominal_setoid_mixin _ rawtypeact_id.

Canonical rawtype_nominalType := @NominalType atom rawtype_choiceType rawtype_nominal_mixin.

Section NominalRawterm.

Inductive rawterm : Type :=
| rVar of term_atom
| rLam of term_atom & rawtype & rawterm
| rApp of rawterm & rawterm
| rAbs of type_atom & kind & rawterm
| rtApp of rawterm & rawtype.
  
Fixpoint rawterm_support t :=
  match  t with
    | rVar x => [fset x]
    | rLam x T t => x |` (rawtype_support T `|` rawterm_support t)
    | rApp t1 t2 => rawterm_support t1 `|` rawterm_support t2
    | rAbs X k t => X |` rawterm_support t
    | rtApp t T => rawterm_support t `|` rawtype_support T
  end.

Fixpoint rawtermact (π : {finperm atom}) t :=
  match t with
    |rVar x => rVar (π x)
    |rLam x T t => rLam (π x) (rawtypeact π T) (rawtermact π t)
    |rApp t1 t2 => rApp (rawtermact π t1) (rawtermact π t2)
    |rAbs X k t => rAbs (π X) k (rawtermact π t)
    |rtApp t T => rtApp (rawtermact π t) (rawtypeact π T)
  end.

Definition rawterm_encode : rawterm -> GenTree.tree atom. Admitted.
Definition rawterm_decode : GenTree.tree atom -> rawterm. Admitted.

Lemma rawterm_codeK : cancel rawterm_encode rawterm_decode.
Proof. Admitted. 

Definition rawterm_eqMixin := CanEqMixin rawterm_codeK.
Canonical rawterm_eqType := EqType rawterm rawterm_eqMixin.
Definition rawterm_choiceMixin := CanChoiceMixin rawterm_codeK.
Canonical rawterm_choiceType := ChoiceType rawterm rawterm_choiceMixin.
Definition rawterm_countMixin := CanCountMixin rawterm_codeK.
Canonical rawterm_countType := CountType rawterm rawterm_countMixin.

Lemma rawtermact1 : rawtermact (1 atom) =1 id.
Proof.
elim => [x|x T t IHt|t1 IHt1 t2 IHt2|X k t IHt|t IHt T];
by rewrite /= ?rawtypeact1 ?finsfun1 ?IHt ?IHt1 ?IHt2 ?IHt.
Qed.

Lemma rawtermactM π π' t : rawtermact (π * π') t = rawtermact π (rawtermact π' t).
Proof.
elim: t => [x|x T t IHt|t1 IHt1 t2 IHt2|X k t IHt|t IHt T];
by rewrite /= ?rawtypeactM ?finsfunM ?IHt1 ?IHt2 ?IHt.
Qed.

Lemma rawtermactproper : forall t1 t2 π, t1 = t2 -> (rawtermact π t1) = (rawtermact π t2).
Proof. by move => t1 t2 π ->. Qed.

Definition rawterm_nominal_setoid_mixin := 
  @PermSetoidMixin rawterm (@eq rawterm) atom rawtermact rawtermact1 
                   rawtermactM rawtermactproper.   

Lemma rawtermact_id (π : {finperm atom}) t :
     (forall a : atom, a \in rawterm_support t -> π a = a) -> rawtermact π t = t.
Proof.
elim: t => [x|x T t IHt|t1 IHt1 t2 IHt2|X k t IHt|t IHt T] /= Hsupp.
  - rewrite  Hsupp //. by rewrite in_fset1.
  - rewrite rawtypeact_id ?IHt ?Hsupp // => [|b b_supp_t|b b_supp_T].
      + exact: fset1U1.
      + apply/Hsupp/fset1Ur/fsetUP. by right.
      + apply/Hsupp/fset1Ur/fsetUP. by left.
  - rewrite IHt1 ?IHt2 // => a a_supp_T;
    by rewrite ?Hsupp // in_fsetU a_supp_T ?orbT //.
  - rewrite IHt ?Hsupp // => [|b b_supp_t].
      + exact: fset1U1.
      + exact/Hsupp/fset1Ur.
  - rewrite IHt ?rawtypeact_id // => [a a_supp_t|a a_supp_T].
      + apply/Hsupp/fsetUP. by right.
      + apply/Hsupp/fsetUP. by left.
Qed.

End NominalRawterm.

Definition rawterm_nominal_mixin :=
  @NominalMixin rawterm_choiceType atom rawterm_nominal_setoid_mixin _ rawtermact_id.

Canonical rawterm_nominalType := @NominalType atom rawterm_choiceType rawterm_nominal_mixin.

Section TypeAlphaEquivalence.

Fixpoint rawtype_depth (T : rawtype) : nat :=
  match T with 
    | rTVar _ => 0
    | rTArrow T1 T2 => (maxn (rawtype_depth T1) (rawtype_depth T2)).+1
    | rTAll _ _ T => (rawtype_depth T).+1
  end.

Lemma raw_depth0var t : raw_depth t = 0 -> exists x, t = rVar x.
Proof. case: t => // a _. by exists a. Qed.

Lemma raw_depth_perm (π : finPerm) t : raw_depth (π \dot t) = raw_depth t.
Proof. by elim: t => [x|u ihu v ihv|x u ihu] //=; rewrite ?ihu ?ihv. Qed.

Lemma strong_termsupport (t : rawterm_nominalType) : 
  forall π, π \dot t = t -> (forall a : atom, a \in support t -> π a == a).
Proof.
elim: t => [a π πa_eq_a b|t iht u ihu π eq_tu a|a t iht π eq_at b].
  - rewrite in_fset1 => /eqP ->. by case: πa_eq_a => ->.
  - rewrite in_fsetU => /orP; case.
      apply iht; by case: eq_tu.
    apply ihu; by case: eq_tu.
  - rewrite in_fset1U => /orP; case.
      by move/eqP ->; case: eq_at => /eqP.
    apply iht; by case: eq_at.
Qed.


(* coq bug : la définition Fixpoint alpha t1 t2 n := ... provoque l'erreur
Anomaly: replace_tomatch. Please report. *)

Fixpoint alpha_rec n t1 t2 :=
  match n, t1, t2 with
      | n, rVar a1, rVar a2 => a1 == a2
      | S n, rApp u v, rApp u' v' => alpha_rec n u u' && alpha_rec n v v'
      | S n, rLambda a u, rLambda a' u' => 
       let z := fresh_in (a,u,a',u') in 
       alpha_rec n (swap a z \dot u) 
             (swap a' z \dot u')
      |_, _, _ => false
  end.

Definition alpha t t' := alpha_rec (raw_depth t) t t'.

Lemma alpha_recE n t t' : (raw_depth t <= n) -> alpha_rec n t t' = alpha t t'.
Proof.
rewrite /alpha; move: {-2}n (leqnn n).
elim: n t t' => //= [|n ihn] [x|u v|x u] [y|u' v'|y u'] [|m] //=.
  rewrite !ltnS geq_max => lmn /andP [um vm]. 
  rewrite !ihn // ?(leq_maxl, leq_maxr) ?geq_max
             ?(leq_trans um, leq_trans vm) //.
rewrite !ltnS => lmn um. by rewrite ihn // ?raw_depth_perm. 
Qed.

Lemma alpha_VarE x y : alpha (rVar x) (rVar y) = (x == y).
Proof. by rewrite/alpha /=. Qed.

Lemma alpha_appE t u t' u' : 
  alpha (rApp t u) (rApp t' u') = alpha t t' && alpha u u'.
Proof. by rewrite/alpha /= !alpha_recE // ?leq_maxl ?leq_maxr. Qed.

Lemma alpha_lamE x t y u : 
  alpha (rLambda x t) (rLambda y u) = 
  let z := fresh_in (x,t,y,u) in
  alpha (swap x z \dot t) (swap y z \dot u).
Proof. by rewrite /alpha /= raw_depth_perm. Qed.


Lemma alpha_equivariant (t t' : rawterm_nominalType) π :
  alpha (π \dot t) (π \dot t') = alpha t t'.
Proof.
rewrite /alpha raw_depth_perm.
move: {-1}(raw_depth t) (leqnn (raw_depth t)) => n.
elim: n t t' π => [|n ihn] [x|u v|x u] [y|u' v'|y u'] π //=;
  do ?by rewrite (inj_eq (@finperm_inj π)). 
  rewrite ltnS geq_max => /andP [un vn] //. rewrite (ihn _ _ π)//.
  by rewrite -[_ v v'](ihn _ _ π).
rewrite ltnS.
set a' := fresh_in _. set a := fresh_in _.
rewrite -[a'](finpermVK π) -!actM -!tfinperm_conj => ru_lt_n. 
have u_fix : swap a (π^-1 a') \dot u = u.
  apply/fresh_transp; first by freshTac.
  apply/im_fresh; rewrite finperm_invK. by freshTac.
have u'_fix : swap a (π^-1 a') \dot u' = u'.
  apply/fresh_transp; first by freshTac.
  apply im_fresh; rewrite finperm_invK. by freshTac.
rewrite -{2}u_fix -{2}u'_fix -(ihn _ _ (π^-1)) ?raw_depth_perm //.
rewrite -!actM 2?finperm_mulA !finperm_invP !finperm_oneP. 
rewrite -(ihn _ _ (swap a (π^-1 a'))) ?raw_depth_perm //.
rewrite -!actM tfinperm_conj [_ * swap y _]tfinperm_conj !tfinpermR !tfinpermNone //
-finperm_can2eq !fresh_neq_in // in_fsetU in_fsetU in_fsetU ?in_fset1 eqxx ?orbT //.
Qed.

Lemma alpha_equivariantprop : equivariant_prop alpha.
Proof. move => π t t' /=. by rewrite alpha_equivariant. Qed.

Lemma alpha_lamP x t y u : 
  reflect (\new a, alpha (swap x a \dot t) (swap y a \dot u))
          (alpha (rLambda x t) (rLambda y u)).
Proof.
move : (equi_funprop (@swap_equiv rawterm_nominalType) alpha_equivariantprop) =>
 /= Requi.
apply (iffP idP).
  rewrite alpha_lamE /= => xtαyu. 
  apply (fresh_new Requi ((x,t),(y,u))) => /=. by admit.
move/(fresh_new Requi ((x,t), (y, u))). rewrite alpha_lamE /=.
Admitted.

Lemma alpha_refl : reflexive alpha.
Proof.
rewrite /alpha.
elim =>[a|t iht u ihu|a t iht] //=.
  rewrite !alpha_recE ?leq_maxl ?leq_maxr /alpha //. by apply/andP.
by rewrite alpha_recE ?raw_depth_perm ?alpha_equivariant.
Qed.

Lemma alpha_sym : symmetric alpha.
Proof.
move => t u; rewrite/alpha.
move: {-1}(raw_depth t) (leqnn (raw_depth t)) => n.
elim: n t u => [|n ihn] [x|t1 u1|x t] [y|t2 u2|y u] //=.
  rewrite ltnS geq_max => /andP [t1_lt_n u1_lt_n].
  by rewrite !ihn // !alpha_recE ?leq_maxl ?leq_maxr //.
rewrite ltnS => t_lt_n.
rewrite ihn raw_depth_perm.
Admitted.

Lemma alpha_trans : transitive alpha.
Proof.
move => u t v.
move: {-1}(raw_depth t) (leqnn (raw_depth t)) => n.
elim: n t u v => [|n ihn] [x|t1 u1|x t] [y|t2 u2|y u] [z|t3 u3|z v]//=;
  do ?(move=> _ ;apply eq_op_trans).
  rewrite ltnS geq_max !alpha_appE => /andP [t1_lt_n u1_lt_n] /andP [t1αt2] [u1αu2]
    /andP [t2αt3 u2αu3].
  apply/andP; split. 
    apply (ihn _ t2) => //.
  by apply (ihn _ u2).
rewrite ltnS => t_lt_n.
move => /alpha_lamP [S HS] /alpha_lamP [S' HS'].
apply/alpha_lamP. exists (S `|` S') => a /fresh_fsetP.
rewrite in_fsetU negb_or => /andP [/fresh_fsetP aFs /fresh_fsetP aFS'].
apply (ihn _ (swap y a \dot u)); first by rewrite raw_depth_perm.
  exact: HS.
exact: HS'.
Qed.

Canonical alpha_equiv := 
  EquivRel alpha alpha_refl alpha_sym alpha_trans.

Definition term := {eq_quot alpha}.
Definition term_eqMixin := [eqMixin of term].
Canonical term_eqType := EqType term term_eqMixin.
Canonical term_choiceType := Eval hnf in [choiceType of term].
Canonical term_countType := Eval hnf in [countType of term].
Canonical term_quotType := Eval hnf in [quotType of term].
Canonical term_eqQuotType := Eval hnf in [eqQuotType alpha of term].
