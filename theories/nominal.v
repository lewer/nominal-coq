From Ssreflect
Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq fintype.

From MathComp
Require Import bigop  finfun finset generic_quotient perm tuple fingroup.
Require Import finperm.
Require Import finmap.
Require Import finsfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope finperm_scope with fperm.
Local Open Scope finperm_scope.
Local Open Scope fset.
Local Open Scope quotient_scope.

Section NominalDef.

Implicit Types (π : finPerm).

Record perm_setoid_mixin (X : Type) (R : X -> X -> Prop) := PermSetoidMixin {
  act : finPerm -> X -> X;
  _ : forall x, R ((act 1) x) x;
  _ : forall π π' x, R (act (π * π') x) (act π (act π' x));
  _ : forall x y π, R x y -> R (act π x) (act π y)
}.

Record nominal_mixin (X : choiceType) := NominalMixin {
  perm_setoid_of : @perm_setoid_mixin X (@eq X);
  supp : X -> {fset atom}; 
  _ : forall π x, 
        (forall a : atom, a \in supp x -> π a = a) -> (act perm_setoid_of π x) = x
}.
                                    
Record nominalType := NominalType {
                           car :> choiceType;
                           nominal_mix : nominal_mixin car }.

Definition actN nt := act (perm_setoid_of (nominal_mix nt)).


End NominalDef.

Notation "π \dot x" := (actN π x)
                         (x at level 60, at level 60).
Notation swap := tfinperm.


Section BasicNominalTheory.

Variables (W X Y Z : nominalType).
Implicit Types (π : finPerm) (x : X).

Local Notation act π := (@actN X π).
Local Notation support := (supp (nominal_mix X)).

Lemma act1 : act 1 =1 id.
Proof. by case: X => car; case; case. Qed.

Lemma actM (π1 π2 : finPerm) : forall x : X,  (π1 * π2) \dot x = π1 \dot (π2 \dot x).
Proof. by case: X => car; case; case. Qed.

Lemma act_id π : forall x : X, (forall a : atom, a \in support x -> π a = a) 
                   -> (act π x) = x.
Proof. case: X => car. case => ps supp. exact. Qed.

Lemma actK π : cancel (act π) (act π^-1).
Proof. by move => x; rewrite -actM (finperm_invP π) act1. Qed.

Lemma actVK π : cancel (act π^-1) (act π).
Proof. by move => x; rewrite -actM (finperm_invVP π) act1. Qed.

Lemma act_inj π : injective (act π).
Proof. by move => x y /(congr1 (act π^-1)); rewrite !actK. Qed.

End BasicNominalTheory.

Definition support (nt : nominalType) x := supp (nominal_mix nt) x.

Section NominalProd.

Variables (X Y : nominalType).
Implicit Type (x : X * Y).

Definition prodact π x := (π \dot x.1, π \dot x.2).

Lemma prodact1 : forall x, prodact 1 x = x.
Proof. by case => x y; rewrite /prodact !act1. Qed.

Lemma prodactM π π' : forall x, prodact (π * π') x = prodact π (prodact π' x).
Proof. by case => x y /=; rewrite /prodact !actM. Qed.

Lemma prodactproper : forall x y π, x = y -> (prodact π x) = (prodact π y).
Proof. by move => x y π ->. Qed.

Definition prod_nominal_setoid_mixin := 
  @PermSetoidMixin (X * Y) (@eq (X * Y)) prodact prodact1 prodactM prodactproper.   

Lemma prodact_id (π : finPerm) x :
     (forall a, a \in (support x.1 `|` support x.2) -> π a = a) -> prodact π x = x.
Proof. 
case: x => x y Hsupp. rewrite /prodact !act_id //= => a asupp; apply Hsupp;
rewrite in_fsetU asupp ?orbT //.
Qed.

Canonical prod_nominal_mixin :=
  @NominalMixin _ prod_nominal_setoid_mixin _ prodact_id.

Canonical prod_nominal_type :=
  NominalType prod_nominal_mixin.

Lemma prodactE π (y : X) (z : Y) : π \dot (y, z) = (π \dot y, π \dot z).
Proof. by []. Qed.

End NominalProd.

(* Lemma strong_prodctsupport π a : *)
(*   atomact π a = a -> (forall b, b \in fset1 a -> atomact π b = b). *)
(* Proof. move => /= πa_eq_a b. by rewrite in_fset1 => /eqP ->. Qed. *)


Section NominalAtoms.

Implicit Types (π : finPerm) (a : atom).

Definition atomact π a := π a.

Lemma atomact1 : forall (a : atom), atomact 1 a = a.
Proof. by move => a /=; rewrite /atomact finsfun1. Qed.

Lemma atomactM : forall π π' a, atomact (π * π') a = atomact π (atomact π' a).
Proof. by move => π π' a /=; rewrite /atomact finsfunM. Qed.

Lemma atomactproper : forall x y π, x = y -> (atomact π x) = (atomact π y).
Proof. by move => x y π ->. Qed.

Definition atom_nominal_setoid_mixin := 
  @PermSetoidMixin atom (@eq atom) atomact atomact1 atomactM atomactproper.   

Lemma atomact_id π a :
     (forall b, b \in fset1 a -> atomact π b = b) -> atomact π a = a.
Proof. apply. by rewrite in_fset1. Qed.

Lemma strong_atomactsupport π a :
  atomact π a = a -> (forall b, b \in fset1 a -> atomact π b = b).
Proof. move => /= πa_eq_a b. by rewrite in_fset1 => /eqP ->. Qed.

Canonical atom_nominal_mixin :=
  @NominalMixin nat_choiceType atom_nominal_setoid_mixin _ atomact_id.

Canonical atom_nominal_type :=
  @NominalType nat_choiceType atom_nominal_mixin.

Lemma swapL a b : (swap a b) \dot a = b. 
Proof. by rewrite /actN /= /atomact tfinpermL. Qed.

Lemma swapR a b : (swap a b) \dot b = a.
Proof. by rewrite /actN /= /atomact tfinpermR. Qed.

Lemma atomactE π a : π \dot a = π a.
Proof. by []. Qed.

End NominalAtoms.



Section NominalAtomSubsets.

Implicit Types (π : finPerm) (A : {fset atom}).

Definition ssatomact π A := im π A. 

Lemma ssatomact1 : forall A, ssatomact 1 A = A.
Proof. 
move => A /=; rewrite -{2}[A](im_id A). apply im_eq1 => a.
by rewrite finsfun1.
Qed.

Lemma ssatomactM : forall π π' A, ssatomact (π * π') A = ssatomact π (ssatomact π' A).
Proof.
move => π π' A /=; rewrite /ssatomact -imM. apply im_eq1 => a.
by rewrite finsfunM.
Qed.

Lemma ssatomactproper : forall A B π, A = B -> (ssatomact π A) = (ssatomact π B).
Proof. by move => A B π ->. Qed. 

Lemma ssatomact_id π A :
  (forall b, b \in A -> π b = b) -> ssatomact π A = A.
Proof. 
move => Asupp /=; apply/fsetP => a; apply/imfsetP/idP => [[b bA]->|aA].
  rewrite Asupp; exact: valP.
exists (FSetSub aA) => //. by rewrite Asupp.
Qed.

(* bricolage *)

Definition code (A : {fset atom}) := fset_keys A.
Definition decode (s : seq atom) := seq_fset s.

Lemma fset_codeK : cancel code decode.
Proof. 
Admitted.


Definition finSet_ChoiceMixin := CanChoiceMixin fset_codeK.
Canonical finset_choiceType := Eval hnf in ChoiceType {fset atom} finSet_ChoiceMixin.
(* --- *)

Definition ssatom_nominal_setoid_mixin := 
  @PermSetoidMixin {fset atom} (@eq {fset atom}) ssatomact ssatomact1 ssatomactM ssatomactproper. 

Canonical ssatom_nominal_mixin :=
  @NominalMixin finset_choiceType ssatom_nominal_setoid_mixin _ ssatomact_id.

Canonical ssatom_nominal_type :=
  @NominalType finset_choiceType ssatom_nominal_mixin. 

Lemma mem_imperm π A (a : atom) : (π a \in π \dot A) = (a \in A).
Proof. by apply/mem_im/finperm_inj. Qed.

End NominalAtomSubsets. 

Section NominalBool.

Implicit Types (π : finPerm) (b : bool).

Definition boolact π b := b.

Lemma boolact1 : forall b, boolact 1 b = b.
Proof. by []. Qed.

Lemma boolactM : forall π π' b, boolact (π * π') b = boolact π (boolact π' b).
Proof. by []. Qed.

Lemma boolactproper : forall b b' π, b = b' -> (boolact π b) = (boolact π b').
Proof. by move => b b' π ->. Qed. 

Lemma boolact_id π b :
  (forall a, a \in fset0 -> π a = a) -> boolact π b = b.
Proof. by []. Qed.

Definition bool_nominal_setoid_mixin := 
  @PermSetoidMixin bool (@eq bool) boolact boolact1 boolactM boolactproper. 

Canonical bool_nominal_mixin :=
  @NominalMixin bool_choiceType bool_nominal_setoid_mixin _ boolact_id.

Canonical bool_nominal_type :=
  @NominalType bool_choiceType bool_nominal_mixin. 

Lemma boolactE π b : π \dot b = b.
Proof. by []. Qed.

End NominalBool.


Section Freshness.

Implicit Types (X Y: nominalType).

Definition max (A : {fset atom}) := \max_(a : A) val a. 

Definition fresh_in X (x : X) := (max (support x)).+1. 

Definition supports X (A : {fset atom}) (x : X) := 
  forall (π : finPerm), (forall a : atom, a \in A -> π a = a) -> π \dot x = x.

Lemma supportsP (X : nominalType) (x : X) :
  supports (support x) x.
Proof.
move => π. 
exact: act_id.
Qed.

Lemma supportsI (X : nominalType) (A B : {fset atom}) (x : X) : 
  supports A x -> supports B x -> supports (A `&` B) x. 
Proof.
(* suppose le théorème de décomposition des permutations en 
   produit de transpositions *)
Admitted.

Definition fresh X a (x : X) := exists S, a \notin S /\ supports S x. 

Notation "a # x" := (fresh a x) (at level 0).

Lemma fresh_notin (A : {fset atom}) : (fresh_in A) \notin A.
Proof.
Admitted.

Lemma freshP X (x : X) : (fresh_in x) # x.
Proof.
exists (support x).
split.
  exact: fresh_notin.
exact: supportsP.
Qed.

Lemma fresh_subsetnotin (A B: {fset atom}) : A `<=` B -> (fresh_in B) \notin A. 
Proof.
move => /fsubsetP AinclB. have: (fresh_in B) \notin B by exact: fresh_notin.
by apply/contra/AinclB.
Qed.

Lemma fresh_support X a (x : X) : a \notin (support x) -> a # x.
Proof.
move => aNx. exists (support x).
split => //.
exact: supportsP.
Qed.

Lemma fresh1U A a : fresh_in (a |` A) != a.
Proof.
have : fresh_in (a |` A) \notin [fset a].
  apply/fresh_subsetnotin/fsubsetP => x. rewrite in_fset1 => /eqP ->.
  by rewrite in_fset1U eqxx.
apply contraR. rewrite negbK => /eqP ->. by rewrite in_fset1.
Qed.

Lemma fresh_neq (A : {fset atom}) a : a \in A -> a != fresh_in A.
Proof. apply contraL => /eqP ->. exact: fresh_notin. Qed.

Lemma fresh_prod X Y a (x : X) (y : Y) : a # (x, y) -> (a # x) /\ (a # y). 
Proof.
move => [S] [aNS supp_S_xy].
split; exists S; split => //; move => π /(supp_S_xy π); rewrite prodactE.
  by move/(congr1 fst).
by move/(congr1 snd).
Qed.

Lemma fresh_transp (X : nominalType) (a b : atom) (x : X) :
      a # x -> b # x -> swap a b \dot x = x.
Proof.
move => [Sa [aNSa supp_Sa_x]] [Sb [bNSb supp_Sb_x]]. 
have supp_SaISb_x : supports (Sa `&` Sb) x by apply: supportsI.
apply supp_SaISb_x => c. rewrite in_fsetI => /andP [cSa cSb].
have aNc : c != a.
  apply/negP => /eqP a_eq_c. move: cSa aNSa.
  by rewrite a_eq_c => ->. 
have bNc : c != b.
  apply/negP => /eqP b_eq_c. move: cSb bNSb.
  by rewrite b_eq_c => ->.
apply tfinpermNone. 
by rewrite aNc bNc.
Qed.

Lemma fresh_perm (X : nominalType) (π : finPerm) (x : X) : 
  [disjoint (support x) & finsupp π] -> π \dot x = x.
Proof.
move => /fdisjointP disj_x_π.  
apply act_id => a /disj_x_π.
exact: finsfun_dflt.
Qed.

End Freshness.

Notation "a # x" := (fresh a x) (at level 0).

Section EquivariantFunctions.

Implicit Types (W X Y Z: nominalType) (π : finPerm).

Definition equivariant1 X Y (f : X -> Y) := forall π x, f (π \dot x) = π \dot (f x). 

Definition equivariant2 X Y Z (f : X -> Y -> Z) := 
  forall π x y,  f (π \dot x) (π \dot y) = π \dot (f x y).

Definition equivariant3 X Y Z W (f :  X -> Y -> Z -> W) :=
  forall π x y z, f (π \dot x) (π \dot y) (π \dot z) = π \dot (f x y z).

Definition equivariant_prop X Y (R : X -> Y -> Prop) :=
  forall π x y, R (π \dot x) (π \dot y) <-> R x y.

Lemma equi_funprop X Y Z (f : X -> Y -> Z) (R : Z -> Z -> Prop) :
  equivariant2 f -> equivariant_prop R -> 
  equivariant_prop (fun (x : X) (y : Y * Y) => R (f x y.1) (f x y.2)). 
Proof.
move => equi_f equi_R π x; case => y y' /=.
by rewrite !equi_f equi_R. 
Qed.

Lemma swap_equiv X : 
  equivariant2 (fun (a : atom) (z : atom * X) => swap z.1 a \dot z.2).
Proof.
move => π a; case => b x /=. by rewrite -!actM tfinperm_conj.
Qed.

End EquivariantFunctions.

Section FinitelySupportedFunctions.

Implicit Types (V W X Y Z : nominalType) (π : finPerm) (S : {fset atom}).

Definition function_support1 X Y (f : X -> Y) S :=
  forall π, [disjoint S & (finsupp π)] -> forall x, π \dot (f x) = f (π \dot x).

Definition finitely_supported1 X Y (f : X -> Y) := 
  exists S, function_support1 f S.

Definition function_support2 X Y Z (f : X -> Y -> Z) S :=
  forall π, [disjoint S & (finsupp π)] -> 
            forall x y, π \dot (f x y) = f (π \dot x) (π \dot y).

Definition finitely_supported2 X Y Z (f : X -> Y -> Z) := 
  exists S, function_support2 f S.


Definition function_support3 X Y Z W (f : X -> Y -> Z -> W) S :=
  forall π, [disjoint S & (finsupp π)] -> 
            forall x y z,  π \dot (f x y z) = f (π \dot x) (π \dot y) (π \dot z).

Definition finitely_supported3 X Y Z W (f : X -> Y -> Z -> W ) := 
  exists S, function_support3 f S.

Definition function_support4 X Y Z W V (f : X -> Y -> Z -> W -> V) S :=
  forall π, [disjoint S & (finsupp π)] -> 
            forall x y z w, 
              π \dot (f x y z w) =
              f (π \dot x) (π \dot y) (π \dot z) (π \dot w).

Definition finitely_supported4 X Y Z W V (f : X -> Y -> Z -> W -> V) := 
  exists S, function_support4 f S.

End FinitelySupportedFunctions.

Section StrongSupport.

Variables (X : nominalType) (S : {fset atom}).
Implicit Types (x : X).

(* hypothèse qui implique que S est le plus petit support de x *)
Hypothesis strong_support : 
  forall x π, π \dot x = x -> (forall a : atom, a \in (support x) -> π a == a).

Lemma equi_support : equivariant1 (@support X).
Proof.
move => π x.
wlog suff : x π / im π (support x) `<=` support (π \dot x).
  move => Hsuff; apply/eqP; rewrite eqEfsubset; apply/andP; split; last by apply Hsuff.
  rewrite -(actVK π (support (π \dot x))) -{2}[x](actK π x);
  exact/im_subset/Hsuff.
apply/fsubsetP => a /imfsetP [b bx] ->. apply contraT => πbNπx.
set c := fresh_in (val b, im π^-1 (support (π \dot x))).
have : swap (val b) c \dot x = x.
  apply (@act_inj _ π). rewrite -actM tfinperm_conj actM fresh_transp //.
    exact: fresh_support πbNπx.
  exists (support (π \dot x)).
  split; last exact: supportsP.
  rewrite -(actVK π (support (π \dot x))) mem_im.
    by admit.  
  exact: finperm_inj.
have {bx} bx : val b \in support x. by apply valP.
move/strong_support => H. move: (H (val b) bx).
rewrite tfinpermL => /eqP cvalb. 
Admitted.

Lemma im_fresh (π : finPerm) a x : (π a) # x <-> a # (π^-1 \dot x).
Proof.
(* en cours *)
Qed.

End StrongSupport.

Section SomeAny.

Variable (X Y : nominalType).

Definition new (P : atom -> Prop) :=
  exists A : {fset atom}, forall a, a \notin A -> P a.

Notation "\new a , P" := (new (fun a:atom => P))
   (format "\new  a ,  P", at level 200).

Theorem some_any (R : atom -> X -> Prop) :
  equivariant_prop R ->
  forall x : X, [/\
      (forall a : atom , a # x -> R a x) -> (\new a, R a x),
      (\new a, R a x) ->  R (fresh_in (support x)) x,
      R (fresh_in (support x)) x -> (exists2 a, a # x & R a x) &
      (exists2 a, a # x & R a x)
      -> (forall a, a # x -> R a x)
    ].
Proof.
move => Requi; split. 
  - exists (support x) => a /fresh_support. exact: (H a).
  - move => [S aNSR].
    apply/(Requi (swap (fresh_in x) (fresh_in (x,S)))).
    rewrite swapL [_ \dot x]fresh_transp; last first. 
      by admit.      
      exact: freshP.
    apply/aNSR. by admit.
  - move => Rfresh. exists (fresh_in x) => //. exact: freshP.
  - move => [a a_fresh_x rax] a' a'_fresh_x.
    case: (eqVneq a a'); first by move <-.
    move => aa'. 
    rewrite -[a'](tfinpermL a a') -[x](fresh_transp a_fresh_x a'_fresh_x) //. 
    by apply/Requi.
Admitted.

Lemma new_forall (R : atom -> X -> Prop) :
  equivariant_prop R ->
  forall x : X, ((\new a, R a x) <-> (forall a, a # x -> R a x)).
Proof.
move=> Requi x. have [? ne ef] := some_any Requi x. 
by split => // /ne /ef.
Qed.

Lemma new_exists  (R : atom -> X -> Prop) :
  equivariant_prop R -> 
  forall x : X, ((\new a, R a x) <-> (exists2 a, a # x & R a x)).
Proof.
move=> Requi x; have [fn nf nh ef] := some_any Requi x.
by split => [/nf/nh|/ef].
Qed.

Lemma fresh_new (R : atom -> X -> Prop) :
  equivariant_prop R ->
  forall x: X, R (fresh_in (support x)) x <-> \new a, R a x. 
Proof.
move=> Requi x. have [fn nf nh ef] := some_any Requi x. 
by split => [/nh/ef/fn | /nf]. 
Qed.

End SomeAny.

Notation "\new a , P" := (new (fun a:atom => P))
   (format "\new  a ,  P", at level 200).
Notation "a # x" := (fresh a x) (at level 0).

Section NominalRawLambdaTerms.

Inductive rawterm : Type :=
| rVar of atom
| rApp of rawterm & rawterm
| rLambda of atom & rawterm.

Fixpoint rawtermact (π : finPerm) t :=
  match t with
    |rVar a => rVar (π a)
    |rApp t1 t2 => rApp (rawtermact π t1) (rawtermact π t2)
    |rLambda a t => rLambda (π a) (rawtermact π t)
  end.

Fixpoint term_support t :=
  match t with
    |rVar a => [fset a]
    |rApp t1 t2 => term_support t1 `|` term_support t2
    |rLambda a t => a |` term_support t
  end.

Fixpoint fv t :=
  match t with
      |rVar a => [fset a]
      |rApp t1 t2 => fv t1 `|` fv t2
      |rLambda a t => fv t `\ a
  end.

Fixpoint rawterm_encode (t : rawterm) : GenTree.tree atom :=
  match t with
    | rVar a => GenTree.Leaf a
    | rLambda a t => GenTree.Node a.+1 [:: rawterm_encode t]
    | rApp t1 t2 => GenTree.Node 0 [:: rawterm_encode t1; rawterm_encode t2]
  end.

Fixpoint rawterm_decode (t : GenTree.tree nat) : rawterm :=
  match t with
    | GenTree.Leaf a => rVar a
    | GenTree.Node a.+1 [:: u] => rLambda a (rawterm_decode u)
    | GenTree.Node 0 [:: u; v] =>
      rApp (rawterm_decode u) (rawterm_decode v)
    | _ =>rVar 0
  end.

Lemma rawterm_codeK : cancel rawterm_encode rawterm_decode.
Proof. by elim=> //= [? -> ? ->|? ? ->]. Qed.

Definition rawterm_eqMixin := CanEqMixin rawterm_codeK.
Canonical rawterm_eqType := EqType rawterm rawterm_eqMixin.
Definition rawterm_choiceMixin := CanChoiceMixin rawterm_codeK.
Canonical rawterm_choiceType := ChoiceType rawterm rawterm_choiceMixin.
Definition rawterm_countMixin := CanCountMixin rawterm_codeK.
Canonical rawterm_countType := CountType rawterm rawterm_countMixin.

Lemma rawtermact1 : rawtermact 1 =1 id.
Proof.
elim => [a | t1 iht1 t2 iht2| a t iht]; 
by rewrite /= ?finsfun1 ?iht1 ?iht2 ?iht.
Qed.

Lemma rawtermactM π π' t : rawtermact (π * π') t = rawtermact π (rawtermact π' t).
Proof.
elim: t => [a | t1 iht1 t2 iht2 | a t iht]; 
by rewrite /= ?finsfunM ?iht1 ?iht2 ?iht.
Qed.

Lemma rawtermactproper : forall t1 t2 π, t1 = t2 -> (rawtermact π t1) = (rawtermact π t2).
Proof. by move => t1 t2 π ->. Qed.

Definition rawterm_nominal_setoid_mixin := 
  @PermSetoidMixin rawterm (@eq rawterm) rawtermact rawtermact1 
                   rawtermactM rawtermactproper.   


Lemma rawtermact_id (π : finPerm) t :
     (forall a : atom, a \in term_support t -> π a = a) -> rawtermact π t = t.
Proof.
elim: t => [a |t1 iht1 t2 iht2|a t iht] /= Hsupp.
  - rewrite  Hsupp //. by rewrite in_fset1.
  - rewrite ?iht1 ?iht2 // => a asuppt; 
    rewrite ?Hsupp // in_fsetU asuppt ?orbT //.
  - rewrite iht ?Hsupp // ?fset1U1 // => b bsuppt. by apply/Hsupp/fset1Ur.
Qed.

End NominalRawLambdaTerms.

Definition rawterm_nominal_mixin :=
  @NominalMixin rawterm_choiceType rawterm_nominal_setoid_mixin _ rawtermact_id.

Canonical rawterm_nominalType := @NominalType rawterm_choiceType rawterm_nominal_mixin.

Section AlphaEquivalence.

Fixpoint raw_depth (t : rawterm) : nat :=
  match t with 
    | rVar _ => 0
    | rApp t1 t2 => (maxn (raw_depth t1) (raw_depth t2)).+1
    | rLambda _ t => (raw_depth t).+1
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
  apply/fresh_transp. by admit.
  rewrite mem_im_supp.
    last by move => x' π'; apply strong_termsupport.    
  apply fresh_subsetnotin.
  rewrite finperm_invK fsubsetU // fsubsetU // fsubsetAA orbT //. 
have u'_fix : swap a (π^-1 a') \dot u' = u'.
  apply/fresh_transp. apply/fresh_subsetnotin/fsubsetU. 
  rewrite fsubsetUr // orbT //. rewrite mem_im_supp; 
    last by move => π' x'; apply strong_termsupport.    
  apply fresh_subsetnotin. rewrite finperm_invK fsubsetU // fsubsetUr // orbT //.
rewrite -{2}u_fix -{2}u'_fix -(ihn _ _ (π^-1)) ?raw_depth_perm //.
rewrite -!actM finperm_mulA finperm_mulA !finperm_invP !finperm_oneP. 
rewrite -(ihn _ _ (swap a (π^-1 a'))) ?raw_depth_perm //.
rewrite -!actM tfinperm_conj [_ * swap y _]tfinperm_conj !tfinpermR !tfinpermNone //
-finperm_can2eq !fresh_neq // in_fsetU in_fsetU in_fsetU ?in_fset1 eqxx ?orbT //.
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
  by apply (fresh_new Requi ((x,t),(y,u))). 
move/(fresh_new Requi ((x,t), (y, u))); by rewrite alpha_lamE.
Qed.

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
by rewrite ihn raw_depth_perm // fsetUC.
Qed.

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
apply/alpha_lamP. exists (S `|` S') => a.
rewrite in_fsetU => /norP [aNS aNS'].
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

(* conflit avec fingroup *)
Notation repr := generic_quotient.repr.

Lemma alpha_eqE t t' : alpha t t' = (t == t' %[mod term]).
Proof. by rewrite piE. Qed.

Definition Var x := lift_cst term (rVar x).
Canonical pi_Var x := PiConst (Var x). 

Definition App := lift_op2 term rApp.
Lemma rAppK : {morph \pi_term : t t' / rApp t t' >-> App t t'}.
Proof.
unlock App => x y /=; apply/eqP.
by rewrite [_ == _]piE alpha_appE !alpha_eqE !reprK !eqxx.
Qed.
Canonical pi_App := PiMorph2 rAppK.

Definition Lambda x := lift_op1 term (rLambda x).
Lemma rLambdaK x : {morph \pi_term : u / rLambda x u >-> Lambda x u}.
Proof.
move => u; unlock Lambda => /=. apply/eqmodP => /=.
by rewrite alpha_lamE //= alpha_equivariant alpha_eqE reprK. 
Qed.
Canonical pi_Lambda x := PiMorph1 (rLambdaK x).

Lemma rVarK x : \pi_term (rVar x) = Var x.
Proof. by rewrite !piE. Qed.

Lemma VarK x : repr (Var x) = rVar x. 
Proof.
have: alpha (repr (Var x)) (rVar x) by rewrite alpha_eqE reprK piE.
by case: (repr (Var x)) => //= m /eqP->.
Qed.

Lemma AppK u v : exists u' v',
    [/\ u = \pi_term u', v = \pi_term v' & repr (App u v) = rApp u' v'].
Proof.
have: alpha (repr (App u v)) (rApp (repr u) (repr v)).
  by rewrite alpha_eqE reprK -[u]reprK -[v]reprK !piE !reprK.
case: (repr (App _ _)) => //= u' v'; rewrite alpha_appE //.
by rewrite !alpha_eqE !reprK => /andP [/eqP <- /eqP <-]; exists u'; exists v'; split.
Qed.

Lemma Var_inj x y : Var x = Var y -> x = y.
Proof.
rewrite !piE => /eqP. 
by rewrite -alpha_eqE alpha_VarE => /eqP. 
Qed.

Lemma App_inj t1 t2 u1 u2 : 
  App t1 t2 = App u1 u2 -> t1 = u1 /\ t2 = u2.
Proof.
move/(congr1 repr). 
have [reprt1 [reprt2 [-> ->]] ->] := AppK t1 t2.
have [repru1 [repru2 [-> ->]] ->] := AppK u1 u2.
move => t1t2_eq_u1u2.
by injection t1t2_eq_u1u2 => -> ->. 
Qed.

End AlphaEquivalence.

(* conflit avec fingroup *)
Notation repr := generic_quotient.repr.

Section NominalTerm.

Implicit Types (π : finPerm) (t : term).

Definition termact π t := \pi_term (π \dot repr t).

Lemma termact1 : termact 1 =1 id.
Proof. move => t /=. by rewrite /termact act1 reprK. Qed.

Lemma termact_equiv π t : 
  π \dot (repr t) == repr (termact π t) %[mod term].   
Proof.
rewrite /termact. rewrite reprK. done.
Qed.

Lemma termactM π π' t : termact (π * π') t = termact π (termact π' t).
Proof.
apply/eqP. 
by rewrite /termact actM piE alpha_equivariant alpha_eqE reprK. 
Qed.

Lemma termactproper : 
  forall t1 t2 π, t1 = t2 -> (termact π t1) = (termact π t2).
Proof. by move => t1 t2 π ->. Qed.

Definition term_nominal_setoid_mixin :=
  @PermSetoidMixin term (@eq term) termact termact1 termactM termactproper.

Lemma termact_id (π : finPerm) t :
     (forall a : atom, a \in term_support (repr t) -> π a = a) -> 
     termact π t = t.
Proof.
rewrite/termact => Hact_id. 
suff : π \dot repr t = repr t by move ->; exact: reprK.
by apply act_id. 
Qed.

Definition term_nominal_mixin :=
  @NominalMixin term_choiceType term_nominal_setoid_mixin _ termact_id.

Canonical term_nominalType := @NominalType term_choiceType term_nominal_mixin.

Lemma pi_equivariant π u : π \dot (\pi_term u) = \pi_term (π \dot u).
Proof.
apply/eqmodP => /=. 
by rewrite alpha_equivariant alpha_eqE reprK. 
Qed.

Lemma repr_equivariant π t : repr (π \dot t) == π \dot (repr t) %[mod term]. 
Proof. by rewrite -pi_equivariant !reprK. Qed.

Lemma eq_lam x t y u : 
  x # (y,u) -> (t = swap x y \dot u) ->
  Lambda x t = Lambda y u.                                                  
Proof.
move/(fresh_prod) => [x_fresh_y x_fresh_u t_swap].
unlock Lambda; apply/eqP; rewrite -alpha_eqE alpha_lamE /= alpha_eqE. 
set z := fresh_in _.
rewrite -!pi_equivariant !reprK.
have xzu : swap x z \dot u = u.  
  apply/fresh_transp => //. apply/fresh_subsetnotin.
  by rewrite fsetUC fsubsetU // fsubsetUr.
rewrite -{2}xzu -!actM tfinperm_conj tfinpermL tfinpermNone ?[_ z y]tfinpermC//.
rewrite fresh_neq; first by rewrite eq_sym x_neq_y.
by rewrite fsetUC in_fsetU in_fsetU in_fset1 eqxx.
Qed.

Lemma Var_equiv π u : π \dot (Var u) = Var (π \dot u).
Proof. by rewrite -rVarK pi_equivariant /= rVarK. Qed.

Lemma App_equiv π t u : π \dot (App t u) = App (π \dot t) (π \dot u).
Proof. 
move: (rAppK (repr t) (repr u)). 
by rewrite !reprK => <-; rewrite pi_equivariant rAppK. 
Qed.

Lemma Lam_equiv π x t : π \dot (Lambda x t) = Lambda (π \dot x) (π \dot t).
Proof.
move: (rLambdaK x (repr t)).
rewrite !reprK => <-; by rewrite pi_equivariant rLambdaK. 
Qed.

Lemma fresh_var x y : x # (Var y) = (x != y).
Proof. by rewrite /support/= VarK/= in_fset1. Qed.

(* Lemma fresh_app x t1 t2 : x # (App t1 t2) = (x # t1) && (x # t2). *)
(* Proof.  *)
(* have [reprt1 [reprt2 [Ht1 Ht2 reprt1t2]]] := AppK t1 t2. *)
(* rewrite /support /= reprt1t2 /= in_fsetU negb_or. *)
(* apply/norP.  *)

End NominalTerm.

Section EliminationPrinciples.

Lemma LambdaK x (u : term) : exists y (v : rawterm),
    [/\ \new z, \pi (swap y z \dot v) = swap x z \dot u  & repr (Lambda x u) = rLambda y v].
Proof.
have: alpha (repr (Lambda x u)) (rLambda x (repr u)).
  by rewrite alpha_eqE reprK -[u]reprK !piE !reprK.
case: (repr (Lambda _ _)) => //= y v /alpha_lamP [S HS].
exists y; exists v. split => //.
exists S => z /HS.
by rewrite alpha_eqE => /eqP.
Qed.

Lemma term_ind (P : term -> Prop) :
  (forall x, P (Var x)) ->
  (forall t1 t2, P t1 -> P t2 -> P (App t1 t2)) ->
  (forall x t, P t -> P (Lambda x t)) ->
              forall u, P u.
Proof.
move => HVar HApp HLam u; rewrite -[u]reprK.
elim: (repr u) => [x|t Ht t' Ht'|a t Ht].
  - by rewrite rVarK.
  - rewrite rAppK. by apply HApp.
  - rewrite rLambdaK. by apply HLam.
Qed.

Definition term_rect (P : term -> Type) :
  (forall x, P (Var x)) ->
  (forall t1 t2, P t1 -> P t2 -> P (App t1 t2)) ->
  (forall x t, P t -> P (Lambda x t)) ->
              forall u, P u.
move => HVar HApp HLam u; rewrite -[u]reprK.
elim: (repr u) => [x|t Ht t' Ht'|a t Ht].
  - by rewrite rVarK.
  - rewrite rAppK. by apply HApp.
  - rewrite rLambdaK. by apply HLam.
Defined.

(* Lemma term_rect_VarE P x f1 f2 f3 : @term_rect P f1 f2 f3 (Var x) = f1 x. *)
(* Proof. *)
(* rewrite /term_rect/=. *)
(* generalize (reprK (Var x)). generalize (repr (Var x)). generalize (Var x) at 2 4. *)
(* apply eq_rect_dep_sym. *)

(* move: (VarK x) => e. case_eq e. *)
(* move: (rVarK x). move <-. *)
(* elim: (repr (Var x)). *)
(* rewrite/term_rect. *)
(* destruct (repr (Var x)). *)
(* rewrite VarK. rewrite reprK. *)

Lemma term_altind_subproof (X : nominalType) (C : X) (P : term -> Prop) :
  (forall x, P (Var x)) ->
  (forall t1 t2, P t1 -> P t2 -> 
                   P (App t1 t2)) ->
  (forall x t, x # C -> P t -> P (Lambda x t)) ->
  forall u π, P (π \dot u).
Proof.
move => HVar HApp HLam.
elim/term_ind => [x π|t1 t2 IHt1 IHt2 π|].
  - rewrite Var_equiv. by apply HVar.
  - rewrite App_equiv. by apply HApp.
  - move => x t HPt π.
    rewrite Lam_equiv. have [xfreshC | xNfreshC] := boolP ((π \dot x) # C).
      by apply HLam.
    pose z := fresh_in (support C `|` support (π \dot x) `|` support (π \dot t)).
    suff : (Lambda (π \dot x) (π \dot t)) = 
           (Lambda z (swap (π \dot x) z \dot (π \dot t))).
      move->; apply HLam; [|rewrite -actM; exact: HPt]. 
      apply/fresh_subsetnotin. by rewrite -fsetUA fsubsetUl.
    apply/sym_eq/eq_lam; last by rewrite tfinpermC.
    apply fresh_subsetnotin. by rewrite -fsetUA fsubsetUr.
Qed.

Lemma term_altind (X : nominalType) (C : X) (P : term -> Prop) :
  (forall x, P (Var x)) ->
  (forall t1 t2, P t1 -> P t2 -> 
                   P (App t1 t2)) ->
  (forall x t, x # C -> P t -> P (Lambda x t)) ->
  forall u, P u.
Proof. 
move => HVar HApp HLam u. rewrite -[u]act1 => *. 
exact: (@term_altind_subproof _ C). 
Qed.


(* freshness condition for binders *)
Definition FCB_supp (X : nominalType) (S : {fset atom}) (f : atom ->  term -> X -> X) :=
  forall a t r, a # S -> a # (f a t r).

Definition FCB (X : nominalType) (f : atom -> term -> X -> X) :=
  exists S, FCB_supp S f.

Variables (X : nominalType) (f1 : atom -> X)
          (f2 : term -> term -> X -> X -> X) 
          (f3 : atom -> term -> X -> X)
          (S1 S2 S3 : {fset atom}).

Hypothesis finsupp_f1 : function_support1 f1 S1.
Hypothesis finsupp_f2 : function_support4 f2 S2.
Hypothesis finsupp_f3 : function_support3 f3 S3.
Hypothesis FCB_f3 : FCB_supp S3 f3. 

Definition depth (t : term) := (raw_depth (repr t)).

Lemma raw_depthα_subproof :
  forall n t1 t2, raw_depth t1 <= n -> 
            alpha t1 t2 -> raw_depth t1 = raw_depth t2.
Proof.
elim => [t1 t2|n IHn t1 t2]. 
  rewrite leqn0 => /eqP /raw_depth0var [x ->].  
  by case: t2.
case: t1; case: t2 => //.
  move => t1 t2 u1 u2 /=. 
  rewrite ltnS /= alpha_appE geq_max => /andP [u1n u2n] /andP [u1t1 u2t2]. 
  by rewrite (IHn u1 t1) // (IHn u2 t2).
move => x t y u /=.
rewrite ltnS alpha_lamE /=. 
set z := fresh_in _.
rewrite -(raw_depth_perm (swap y z)) /= => u_n uαt. 
by rewrite (IHn _ (swap x z \dot t) u_n) ?raw_depth_perm.
Qed.

Lemma raw_depthα t1 t2 :
  alpha t1 t2 -> raw_depth t1 = raw_depth t2.
Proof.
exact: (raw_depthα_subproof (leqnn (raw_depth t1))).
Qed.

Lemma depth0var t : depth t = 0 -> exists x, t = Var x.
Proof.
rewrite/depth => /raw_depth0var [x tVarx].
exists x.
by rewrite -[t]reprK tVarx rVarK.
Qed.

Lemma depth_var x : depth (Var x) = 0.
Proof. by rewrite/depth VarK. Qed.

Lemma depth_perm t π : depth (π \dot t) = depth t.
Proof.
rewrite /depth (@raw_depthα (repr (π \dot t)) (π \dot (repr t))).
  exact: raw_depth_perm.
rewrite alpha_eqE. exact: repr_equivariant.
Qed.

Lemma depth_app t1 t2 : 
  depth (App t1 t2) = (maxn (depth t1) (depth t2)).+1.
Proof.
have [reprt1 [reprt2 [Ht1 Ht2 reprt1t2]]] := AppK t1 t2.
rewrite/depth reprt1t2/=.
apply eq_S. congr maxn.
  rewrite (@raw_depthα reprt1 (repr t1)) //.
  by rewrite alpha_eqE -Ht1 reprK. 
rewrite (@raw_depthα reprt2 (repr t2)) //.
by rewrite alpha_eqE -Ht2 reprK.
Qed.

Lemma depth_lam x t :
  depth (Lambda x t) = (depth t).+1.
Proof.
have [y [u [[S HS]]] repr_xt] := LambdaK x t.
rewrite /depth repr_xt/=.
pose z := fresh_in S.
rewrite -(raw_depth_perm (swap y z)).
rewrite -[X in _ = X.+1](raw_depth_perm (swap x z)).
apply/eq_S/raw_depthα.
rewrite alpha_eqE -[X in _ == X]pi_equivariant reprK.
apply/eqP. exact: (HS z (fresh_notin S)).
Qed.

Lemma depth_repr (t : rawterm) :
  raw_depth t = depth (\pi t).
Proof.
rewrite/depth. apply raw_depthα.
by rewrite alpha_eqE reprK.
Qed.

Variable (dflt : X).

Fixpoint term_altrect_rec n (t : term) :=
  match n, repr t with 
    |_, rVar x => f1 x
    |S n, rApp t1 t2 => f2 (\pi t1) (\pi t2) 
                      (term_altrect_rec n (\pi t1)) 
                      (term_altrect_rec n (\pi t2))
    |S n, rLambda x u => let z := fresh_in ((S1 `|` S2 `|` S3) `|` (support x `|` support t)) in 
                         f3 z (\pi ((swap x z) \dot u)) 
                            (term_altrect_rec n (\pi ((swap x z) \dot u)))
    |_,_ => dflt
  end.

Definition term_altrect (t : term) :=
  term_altrect_rec (depth t) t.

Lemma term_altrect_recE_subproof n m t :
  depth t <= n -> n <= m -> term_altrect_rec n t = term_altrect_rec m t.
Proof.
elim: m n t =>[n t tn|m IHm n t].
  by rewrite leqn0 => /eqP ->.
case: n => [|n].
  rewrite leqn0 => /eqP /depth0var => [[x ->]].
  by rewrite /= VarK.
rewrite ltnS /=.
case_eq (repr t) => // [t1 t2 reprt|x u repru].
  rewrite /depth reprt /= ltnS geq_max => /andP [t1n t2n] nm.
  have deptht1 : depth (\pi t1) <= n 
    by rewrite -depth_repr.
  have deptht2 : depth (\pi t2) <= n 
    by rewrite -depth_repr.
  by rewrite !IHm //.
set z := fresh_in _.
rewrite/depth repru /= ltnS => u_leq_n nm.
have depthu : depth (\pi_(term) u) <= n 
  by rewrite -depth_repr.
congr f3.
apply IHm => //.
by rewrite -pi_equivariant depth_perm.
Qed.

Lemma term_altrect_recE n t :
  depth t <= n -> term_altrect_rec n t = term_altrect t.
Proof.
rewrite/term_altrect => t_leq_n.
symmetry.
by apply term_altrect_recE_subproof.
Qed.

(* Lemma raw_fun_equivariant_subproof t (π: finPerm) : *)
(*     [disjoint S1 & finsupp π] -> *)
(*     [disjoint S2 & finsupp π] -> *)
(*     [disjoint S3 & finsupp π] -> *)
(* π \dot (raw_fun_subproof t) = raw_fun_subproof (π \dot t). *)
(* Proof. *)
(* elim: t => [x S1π _ _|t1 IHt1 t2 IHt2 S1π S2π S3π|x t IHt S1π S2π S3π]. *)
(*   - exact: finsupp_f1.  *)
(*   - rewrite /= finsupp_f2 //. *)
(*     by rewrite IHt1 // IHt2 // !pi_equivariant. *)
(*   - rewrite /= finsupp_f3 //. *)
(*     by rewrite IHt // pi_equivariant. *)
(* Qed. *)

Lemma fset1_disjoint (x : atom) (A B : {fset atom}) : 
  [disjoint x |` A & B] = ((x \notin B) && [disjoint A & B]%fset).
Proof.
apply/idP/idP.
  move/fdisjointP => H; apply/andP; split.
    apply H. by rewrite fset1U1.
  apply/fdisjointP => a /(fsubsetP (fsubsetU1 x A) a). 
  exact: H.
move/andP => [xNB /fdisjointP A_disj_B]; apply/fdisjointP => a.
rewrite in_fset1U => /orP; case.
  by move/eqP ->.
exact: A_disj_B.
Qed.

Lemma term_altrect_VarE x : @term_altrect (Var x) = f1 x.
Proof. by rewrite/term_altrect/depth /= VarK /= VarK. Qed.

Lemma term_altrect_AppE t1 t2 :
  @term_altrect (App t1 t2) = 
  f2 t1 t2 
     (term_altrect t1)
     (term_altrect t2).
Proof.
have [reprt1 [reprt2 [Ht1 Ht2 reprt1t2]]] := AppK t1 t2.
rewrite/term_altrect depth_app /= reprt1t2  -Ht1 -Ht2. 
by rewrite !term_altrect_recE // ?leq_maxl ?leq_maxr.
Qed.

Lemma term_altrect_equivariant t (π : finPerm) :
  [disjoint S1 & finsupp π] ->
  [disjoint S2 & finsupp π] ->
  [disjoint S3 & finsupp π] ->
  π \dot (term_altrect t) = term_altrect (π \dot t).
Proof.
move : {-1}(depth t) (leqnn (depth t)) => n.
elim: n t π => [t π|n IHn t π].
  rewrite leqn0 => /eqP /depth0var => [[x ->]] S1_π S2_π S3_π.
  rewrite Var_equiv !term_altrect_VarE.
  exact: finsupp_f1.
rewrite leq_eqVlt => /orP; case =>[/eqP|]; last by
  rewrite ltnS; exact: IHn.
rewrite /term_altrect depth_perm => depth_t S1_π S2_π S3_π.
rewrite depth_t /=.
have : alpha (repr (π \dot t)) (π \dot (repr t)).
  by rewrite alpha_eqE; exact: repr_equivariant.
case_eq (repr t); case_eq (repr (π \dot t)) => //.
  - move => a repr_πt b repr_t. 
    have -> : π \dot rVar b = rVar (π \dot b) by [].
    rewrite alpha_VarE => /eqP ->.
    exact: finsupp_f1.
  - move => t1 t2 _ u1 u2 repr_t.
    have -> : π \dot (rApp u1 u2) = rApp (π \dot u1) (π \dot u2) by [].
    rewrite alpha_appE !alpha_eqE => /andP [/eqP t1_u1 /eqP t2_u2].
    rewrite t1_u1 t2_u2 finsupp_f2 // !pi_equivariant.
    have depth_u1 : depth (\pi u1) = n by admit.
    have depth_u2 : depth (\pi u2) = n by admit.
    rewrite -{1}depth_u1 -depth_u2 -!pi_equivariant.
    congr f2.
       rewrite depth_u2 -depth_u1 -{2}(depth_perm _ π).
       apply IHn => //. by rewrite depth_u1 leqnn.
    rewrite -{2}(depth_perm _ π). apply IHn => //. by rewrite depth_u2 leqnn.
  - move => y u repr_πt z v repr_t.
    set a := fresh_in _; set b := fresh_in _.
    have aNS1 : a \notin S1 by
      apply/fresh_subsetnotin/fsubsetU/orP; left; rewrite -fsetUA fsubsetUl.
    have aNS2 : a \notin S2 by
      apply/fresh_subsetnotin/fsubsetU/orP; left; apply/fsubsetU; rewrite fsubsetUr.
    have aNS3 : a \notin S3 by
      apply/fresh_subsetnotin/fsubsetU; rewrite fsubsetUr.
    have bNS1 : b \notin S1 by
        apply/fresh_subsetnotin/fsubsetU/orP; left; rewrite -fsetUA fsubsetUl.
    have bNS2 : b \notin S2 by
        apply/fresh_subsetnotin/fsubsetU/orP; left; apply/fsubsetU; rewrite fsubsetUr.      
    have bNS3 : b \notin S3 by
      apply/fresh_subsetnotin/fsubsetU; rewrite fsubsetUr.
    have -> : π \dot (rLambda z v) = rLambda (π \dot z) (π \dot v) by [].
    move => /alpha_lamP [S HS].
    set t1 := \pi_term _; set t2 := \pi_term _.
    pose m := fresh_in ((S `|` S1) `|` (S2 `|` S3 ) `|` (support (π \dot v) `|` support u) `|`
                     (support (f3 a t1 (term_altrect t1)) `|`
                     (π^-1 \dot (support (f3 b t2 (term_altrect t2)))))).
    have mNS1 : m \notin S1 by admit.
    have mNS2 : m \notin S2 by admit.
    have mNS3 : m \notin S3 by admit.
    have depth_zav : n = depth (\pi (swap z a \dot v)).
      move: (congr1 \pi_term repr_t) => /(congr1 depth).
      rewrite reprK depth_t rLambdaK depth_lam -pi_equivariant depth_perm. 
      exact: eq_add_S.
    have depth_ybu : n = depth (\pi (swap y b \dot u)).
      move: (congr1 \pi_term repr_πt) => /(congr1 depth).
      rewrite reprK depth_perm depth_t rLambdaK depth_lam -pi_equivariant depth_perm. 
      exact: eq_add_S.
    rewrite {1}depth_zav depth_ybu.
    rewrite -[f3 a _ _](@fresh_transp _ a m); last first.
      apply/fresh_subsetnotin/fsubsetU/orP; right; apply fsubsetUl.     
      by apply/FCB_f3/fresh_subsetnotin/fsubsetU; rewrite fsubsetUr.
    rewrite finsupp_f3; last exact: tfinperm_disj.
    rewrite swapL finsupp_f3 //. rewrite IHn; 
      try (by apply tfinperm_disj); last first.
      by rewrite depth_zav leqnn.
    rewrite IHn //; last by rewrite depth_perm depth_zav leqnn.                rewrite -[RHS](@fresh_transp _ b (π m)); last first.
      admit.
      exact: FCB_f3.
    rewrite finsupp_f3; last by admit.
    rewrite swapL IHn; last first.
      admit. admit. admit. admit.
    suff : π \dot swap a m \dot t1 = swap b (π m) \dot t2 by move ->. 
    have πmNS : π m \notin S by admit.
    rewrite/t1/t2 -!pi_equivariant.
    rewrite -[swap _ _ \dot _]actM tfinperm_conj tfinpermL tfinpermNone;
      last by admit.
    rewrite actM [swap a m \dot _]fresh_transp; last first.
      admit. admit. 
    move : (HS _ πmNS). rewrite alpha_eqE -!pi_equivariant => /eqP. 
    rewrite -!actM tfinperm_conj => <-. 
    rewrite tfinperm_conj tfinpermL tfinpermNone; last by admit.
    by  rewrite actM [swap b _ \dot _]fresh_transp; last first;
      admit; admit.
Admitted.

Lemma f3α x t y u :
  x \notin S1 `|` S2 `|` S3 -> y \notin S1 `|` S2 `|` S3 -> Lambda x t = Lambda y u ->
  f3 x t (term_altrect t) = f3 y u (term_altrect u).
Proof.
move => xNS1S2S2 yNS1S2S3. 
unlock Lambda => /eqP. rewrite -alpha_eqE => /alpha_lamP [S HS].
pose z := fresh_in (S1 `|` S2 `|` S3 `|` S `|`
                 support (f3 x t (term_altrect t)) `|`
                 support (f3 y u (term_altrect u))).
have zNS3 : z \notin S3 by admit.
have xNS3 : x \notin S3 by admit.
have yNS3 : y \notin S3 by admit.
have <- : (f3 z ((swap x z) \dot t) ((swap x z) \dot (term_altrect t))) = (f3 x t (term_altrect t)).
  rewrite -{1}(swapL x z) -finsupp_f3.
    rewrite fresh_transp //; first exact: FCB_f3.
    apply/fresh_subsetnotin/fsubsetU.
    by rewrite fsubsetUr.
  apply/fdisjointP => b.
  apply contraL => /(fsubsetP (tfinperm_supp x z) b).
  rewrite in_fset2 => /orP. case;
    by move/eqP ->.
have <- : (f3 z ((swap y z) \dot u) ((swap y z) \dot (term_altrect u))) = (f3 y u (term_altrect u)).
  rewrite -{1}(swapL y z) -finsupp_f3.
    rewrite fresh_transp //; first exact: FCB_f3.
    apply/fresh_subsetnotin/fsubsetU.
    by rewrite fsubsetAA orbT.
  apply/fdisjointP => b.
  apply contraL => /(fsubsetP (tfinperm_supp y z) b).
  rewrite in_fset2 => /orP. case;
    by move/eqP ->.
rewrite !term_altrect_equivariant;
  try (apply/fdisjointP; admit).
suff : swap x z \dot t = swap y z \dot u by move ->.
have zNS : z \notin S by admit. 
move : (HS _ zNS). 
by rewrite alpha_eqE -!pi_equivariant !reprK => /eqP.
Admitted.

Lemma term_altrect_LamE x t :
  x \notin (S1 `|` S2 `|` S3) -> 
  @term_altrect (Lambda x t) = f3 x t (term_altrect t).
Proof.
rewrite in_fsetU in_fsetU => /norP [/norP [xNS1 xNS2]] xNS3.
have [y [u [[S HS] repr_xt]]] := LambdaK x t.   
rewrite/term_altrect depth_lam /= repr_xt.
set a := fresh_in _. 
move: (HS _ (fresh_notin S)) => yzu_xzt.
have depth_tu : depth t = depth (\pi (swap y a \dot u)).
  rewrite -pi_equivariant depth_perm.
  rewrite -(depth_perm _ (swap x (fresh_in S))) -yzu_xzt.
  by rewrite -pi_equivariant depth_perm.
have aNS3 : a \notin S3 by admit.
rewrite {1}depth_tu.
apply f3α => //. admit. admit.
rewrite (@eq_lam a _ y (\pi u)).
  move: (congr1 \pi_term repr_xt).
  by rewrite reprK rLambdaK.
admit.
rewrite -pi_equivariant. admit.
Admitted.

End EliminationPrinciples.
