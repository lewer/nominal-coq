(*************************************************************************)
(* Copyright (C) 2012                                                    *)
(* Author C. Cohen                                                       *)
(* All rights reserved                                                   *)
(* Draft - DO NOT DISTRIBUTE                                             *)
(* License to be determined                                              *)
(*************************************************************************)

Require Import ssreflect ssrbool ssrnat eqtype choice ssrfun seq path.
Require Import fintype finfun bigop finset.

(****************************************************************************)
(* This file provides a representation of finitely supported maps where     *)
(* the keys K lie in an ordType and the values V in an arbitrary type.      *)
(*                                                                          *)
(*        {fset K} == finite sets of elements of K                          *)
(*           fset0 == the empty finite set                                  *)
(*        [fset k] == the singleton finite set {k}                          *)
(*                                                                          *)
(*   {fmap K -> V} == finitely supported maps from K to V.                  *)
(*          domf f == finite set ({fset K}) of keys of f                    *)
(*         k \in f == k is a key of f                                       *)
(*          [fmap] == the empty finite map                                  *)
(*      f.[k <- v] == f extended with the mapping k -> v                    *)
(*          f.[~k] == f where the key k has been removed                    *)
(*           f.[p] == returns v if p is a proof of k \in f, and k maps to v *)
(*          f.[?k] == returns Some v if k maps to v, otherwise None         *)
(*          f ++ g == concatenation of f and g,                             *)
(*                    the keys of g override those of f                     *)
(*                                                                          *)
(****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "{fmap T }" (at level 0, format "{fmap  T }").
Reserved Notation "{fset K }" (at level 0, format "{fset  K }").
Reserved Notation "x .[ k <- v ]"
  (at level 2, k at level 200, v at level 200, format "x .[ k  <-  v ]").
Reserved Notation "x .[~ k ]" (at level 2, k at level 200, format "x .[~  k ]").
Reserved Notation "x .[+ k ]" (at level 2, k at level 200, format "x .[+  k ]").
Reserved Notation "x .[? k ]" (at level 2, k at level 200, format "x .[?  k ]").
Reserved Notation "x .[ k | v ]"
  (at level 2, k at level 200, v at level 200, format "x .[ k  |  v ]").
Reserved Infix ":~:" (at level 52).
Reserved Notation "[ 'fset' k ]" (at level 0, k at level 99, format "[ 'fset'  k ]").

Reserved Notation "[ 'fmap' E | k , kf , v <- f ]"
  (at level 0, E at level 99, k ident, kf ident, v ident,
   format "[ '[hv' 'fmap'  E '/ '  |  k ,  kf ,  v  <-  f ] ']'").
Reserved Notation "[ 'fmap' E | k , v <- f ]"
  (at level 0, E at level 99, k ident, v ident,
   format "[ '[hv' 'fmap'  E '/ '  |  k ,  v  <-  f ] ']'").
Reserved Notation "[ 'fmap' E | v <- f ]"
  (at level 0, E at level 99, v ident,
   format "[ '[hv' 'fmap'  E '/ '  |  v  <-  f ] ']'").

Reserved Notation "[ 'fmap' k kf 'in' A => E ]"
   (at level 0, E at level 99, k ident, kf ident,
   format "[ '[hv' 'fmap'  k  kf  'in'  A  =>  '/' E ] ']'").
Reserved Notation "[ 'fmap' k 'in' A => E ]"
   (at level 0, E at level 99, k ident,
   format "[ '[hv' 'fmap'  k  'in'  A  =>  '/' E ] ']'").


Section extra.

Lemma mem_remF (T : eqType) (s : seq T) x : uniq s -> x \in rem x s = false.
Proof. by move=> us; rewrite mem_rem_uniq // inE eqxx. Qed.

Definition ffun0 (T : finType) (X : Type) : #|T| = 0 -> {ffun T -> X}.
Proof. by move=> /card0_eq T0; apply: finfun => t; move: (T0 t). Defined.

Definition oextract (T : Type) (o : option T) : o -> T :=
  if o is Some t return o -> T then fun=> t
  else False_rect T \o 
    @eq_ind bool None (fun e => if e then False else True) I true.

Lemma oextractP (T : Type) (x : T) (xP : Some x) : oextract xP = x.
Proof. by []. Qed.

End extra.

Module Key.
Section ClassDef.
  Structure mixin_of (T : eqType) := Mixin {
    sort_keys : seq T -> seq T;
    _ : forall s : seq T, uniq (sort_keys s);
    _ : forall s : seq T, sort_keys s =i s;
    _ : forall s s' : seq T, s =i s' -> sort_keys s = sort_keys s'
  }.

  Record class_of T := Class {
    base  : Equality.class_of T;
    mixin : mixin_of (@Equality.Pack T base T)
  }.

  Local Coercion base : class_of >-> Equality.class_of.

  Structure type := Pack { sort; _ : class_of sort; _ : Type }.

  Local Coercion sort : type >-> Sortclass.

  Variables (T : Type) (cT : type).

  Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
  Definition clone c of phant_id class c := @Pack T c T.
  Let xT := let: Pack T _ _ := cT in T.
  Notation xclass := (class : class_of xT).

  Definition pack b0 (m0 : mixin_of (@Equality.Pack T b0 T)) :=
    fun b bT & phant_id (Equality.class bT) b =>
    fun    m & phant_id m0 m => Pack (@Class T b m) T.

  Definition eqType := @Equality.Pack cT xclass xT.
End ClassDef.

  Module Import Exports.
    Coercion base   : class_of >-> Equality.class_of.
    Coercion mixin  : class_of >-> mixin_of.
    Coercion sort   : type >-> Sortclass.
    Coercion eqType : type >-> Equality.type.

    Canonical eqType.

    Notation keyType := type.
    Notation keyMixin := mixin_of.
    Notation KeyMixin := Mixin.
    Notation KeyType T m := (@pack T _ m _ _ id _ id).

    Notation "[ 'keyType' 'of' T 'for' cT ]" := (@clone T cT _ id)
      (at level 0, format "[ 'keyType' 'of' T 'for' cT ]") : form_scope.
    Notation "[ 'keyType' 'of' T ]" := (@clone T _ _ id)
      (at level 0, format "[ 'keyType' 'of' T ]") : form_scope.
  End Exports.
End Key.
Import Key.Exports.

Section ChoiceKeyMixin.
Variable (T : choiceType).

Definition choice_sort_keys (s : seq T) : seq T :=
   choose [pred t : seq T | perm_eq (undup s) t] (undup s).

Fact choice_sort_keys_uniq s : uniq (choice_sort_keys s).
Proof.
rewrite /choice_sort_keys; set P := (X in choose X).
have : P (choose P (undup s)) by exact/chooseP/perm_eq_refl.
by move=> /perm_eq_uniq <-; rewrite undup_uniq.
Qed.

Fact mem_choice_sort_keys (s : seq T) : choice_sort_keys s =i s.
Proof.
rewrite /choice_sort_keys; set P := (X in choose X) => x.
have : P (choose P (undup s)) by exact/chooseP/perm_eq_refl.
by move=> /perm_eq_mem <-; rewrite mem_undup.
Qed.

Lemma eq_choice_sort_keys (s s' : seq T) :
  s =i s' -> choice_sort_keys s = choice_sort_keys s'.
Proof.
move=> eq_ss'; rewrite /choice_sort_keys.
have peq_ss' : perm_eq (undup s) (undup s').
  by apply: uniq_perm_eq; rewrite ?undup_uniq // => x; rewrite !mem_undup.
rewrite (@choose_id _ _ _ (undup s')) //=; apply: eq_choose => x /=.
by apply: sym_left_transitive; [exact: perm_eq_sym|exact: perm_eq_trans|].
Qed.

Definition ChoiceKeyMixinOf of (phant T) :=
  KeyMixin choice_sort_keys_uniq mem_choice_sort_keys eq_choice_sort_keys.

End ChoiceKeyMixin.

Notation ChoiceKeyMixin T := (@ChoiceKeyMixinOf _ (Phant T)).

Definition nat_KeyMixin := ChoiceKeyMixin nat.
Canonical nat_KeyType := KeyType nat nat_KeyMixin.

Section KeyTheory.
Variable (K : keyType).
Implicit Types (k : K) (ks : seq K).

Definition sort_keys ks := Key.sort_keys (Key.class K) ks.

Lemma sort_keys_uniq ks : uniq (sort_keys ks).
Proof. by rewrite /sort_keys; case: K ks => [? [? []]]. Qed.

Lemma sort_keysE ks : sort_keys ks =i ks.
Proof. by rewrite /sort_keys; case: K ks => [? [? []]]. Qed.
Hint Resolve sort_keysE.

Lemma mem_sort_keys ks k : k \in ks -> k \in sort_keys ks.
Proof. by rewrite sort_keysE. Qed.

Lemma mem_sort_keys_intro ks k : k \in sort_keys ks -> k \in ks.
Proof. by rewrite sort_keysE. Qed.

Lemma eq_sort_keys {ks ks'} : (ks =i ks') <-> (sort_keys ks = sort_keys ks').
Proof.
split=> eq_ks; last first.
  by move=> k; rewrite -sort_keysE eq_ks sort_keysE.
by rewrite /sort_keys; case: K ks ks' eq_ks => [? [? []]].
Qed.

Lemma sort_keys_nil : sort_keys [::] = [::].
Proof.
have := sort_keysE [::].
by case: sort_keys => //= a l /(_ a); rewrite mem_head.
Qed.

Lemma sort_keys_id ks : sort_keys (sort_keys ks) = sort_keys ks.
Proof. by have /eq_sort_keys := sort_keysE ks. Qed.

Definition canonical_keys ks := sort_keys ks == ks.

Lemma canonical_uniq ks : canonical_keys ks -> uniq ks.
Proof. by move=> /eqP <-; exact: sort_keys_uniq. Qed.

Lemma canonical_sort_keys ks : canonical_keys (sort_keys ks).
Proof. by rewrite /canonical_keys sort_keys_id. Qed.

Lemma canonical_eq_keys ks ks' :
  canonical_keys ks -> canonical_keys ks' ->
  ks =i ks' -> ks = ks'.
Proof.
move=> /eqP; case: _ /; move=> /eqP; case: _ / => eq_ks_ks'.
by apply/eq_sort_keys => x; rewrite -sort_keysE eq_ks_ks' sort_keysE.
Qed.

Lemma size_sort_keys ks : size (sort_keys ks) = size (undup ks).
Proof.
rewrite -(iffLR eq_sort_keys (mem_undup _)); symmetry.
by apply/eqP; rewrite -uniq_size_uniq ?sort_keys_uniq ?undup_uniq.
Qed.

End KeyTheory.

Arguments eq_sort_keys {K ks ks'}.

Section Def.
Variables (K : keyType).

Structure finSet : Type := mkFinSet {
  fset_keys : seq K;
  _ : canonical_keys fset_keys
}.

Definition finset_of (_ : phant K) := finSet.
End Def.

Notation "{fset T }" := (@finset_of _ (Phant T)) : type_scope.

Definition pred_of_finset (K : keyType)
  (f : {fset K}) : pred K := mem (fset_keys f).
Canonical finSetPredType (K : keyType) :=
  Eval hnf in mkPredType (@pred_of_finset K).

Coercion Type_of_finSet (K : keyType) (s : finSet K) : Type := seq_sub (fset_keys s).

Section Basics.
Variables (K : keyType).

Lemma keys_canonical (f : {fset K}) : canonical_keys (fset_keys f).
Proof. by case: f. Qed.

End Basics.

Hint Resolve keys_canonical.
Hint Resolve sort_keys_uniq.

Canonical  finSetSubType K := [subType for (@fset_keys K)].
Definition finSetEqMixin (K : keyType) := [eqMixin of {fset K} by <:].
Canonical  finSetEqType  (K : keyType) := EqType {fset K} (finSetEqMixin K).

(* Definition mem_pred_of_finset (K : keyType) (A : {fset K}) := mem [finType of A]. *)

Section Ops.

Context {K : keyType}.
Implicit Types (a b c : K) (A B C D : {fset K}) (s : seq K).

(* Definition FinSet V (kvs : K * V) : *)
(*   canonical_keys (keys []). *)

Definition fset0 : {fset K} :=
  @mkFinSet K [::] (introT eqP (@sort_keys_nil K)).

Definition fset s : {fset K} := mkFinSet (canonical_sort_keys s).

Definition fset1U a A : {fset K} := fset (a :: fset_keys A).

Definition fset1 a : {fset K} := fset [:: a].

Definition fsetU A B := fset (fset_keys A ++ fset_keys B).

Definition fsetI A B := fset [seq x <- fset_keys A | x \in fset_keys B].

Definition fsetD A B := fset [seq k <- fset_keys A | k \notin fset_keys B].

Definition fsubset A B := fsetI A B == A.

Definition fproper A B := fsubset A B && ~~ fsubset B A.

Definition FSet A (X : {set A}) : {fset K} :=
  fset [seq val x | x <- enum X].

End Ops.

(* Coercion FSet : set_of >-> finset_of. *)

Delimit Scope fset_scope with fset.
Local Open Scope fset_scope.

Notation "[ 'fset' a ]" := (fset1 a)
  (at level 0, a at level 99, format "[ 'fset'  a ]") : fset_scope.
Notation "[ 'fset' a : T ]" := [fset (a : T)]
  (at level 0, a at level 99, format "[ 'fset'  a   :  T ]") : fset_scope.
Notation "A :|: B" := (fsetU A B) : fset_scope.
Notation "a |: A" := ([fset a] :|: A) : fset_scope.
(* This is left-associative due to historical limitations of the .. Notation. *)
Notation "[ 'fset' a1 ; a2 ; .. ; an ]" := (fsetU .. (a1 |: [fset a2]) .. [fset an])
  (at level 0, a1 at level 99,
   format "[ 'fset'  a1 ;  a2 ;  .. ;  an ]") : fset_scope.
Notation "A :&: B" := (fsetI A B) : fset_scope.
Notation "A :\: B" := (fsetD A B) : fset_scope.
Notation "A :\ a" := (A :\: [fset a]) : fset_scope.

Notation "A \fsubset B" := (fsubset A B)
  (at level 70, no associativity) : bool_scope.

Notation "A \fproper B" := (fproper A B)
  (at level 70, no associativity) : bool_scope.

Section Theory.

Variables (K : keyType).
Implicit Types (a b x : K) (A B C D : {fset K}) (pA pB pC : pred K) (s : seq K).

Lemma in_fset s : fset s =i s.
Proof. by move=> a; rewrite sort_keysE. Qed.

Lemma in_fset_in x s : x \in fset s -> x \in s.
Proof. by rewrite in_fset. Qed.

Lemma in_fsetT x s : x \in s -> x \in fset s.
Proof. by rewrite in_fset. Qed.

Lemma fsetP {A B} : A =i B <-> A = B.
Proof. by split=> [eqAB|-> //]; apply/val_inj/canonical_eq_keys => //=. Qed.

Lemma fset_eqP {A B} : reflect (A =i B) (A == B).
Proof. exact: (equivP eqP (iff_sym fsetP)). Qed.

Lemma in_fset0 x : x \in fset0 = false.
Proof. by rewrite inE. Qed.

Lemma in_fset1U a' A a : (a \in a' |: A) = (a == a') || (a \in A).
Proof. by rewrite !(inE, sort_keysE, in_cons, mem_cat, orbF). Qed.

Lemma in_fset1 a' a : a \in [fset a'] = (a == a').
Proof. by rewrite !(inE, sort_keysE, in_cons, mem_cat, orbF). Qed.

Lemma in_fsetU A B a : (a \in A :|: B) = (a \in A) || (a \in B).
Proof. by rewrite !(inE, sort_keysE, mem_cat). Qed.

Lemma in_fsetI A B a : (a \in A :&: B) = (a \in A) && (a \in B).
Proof. by rewrite !inE /= !sort_keysE !mem_filter andbC. Qed.

Lemma in_fsetD A B a : (a \in A :\: B) = (a \notin B) && (a \in A).
Proof. by rewrite !inE /= !sort_keysE !mem_filter. Qed.

Lemma in_fsetD1 A b a : (a \in A :\ b) = (a != b) && (a \in A).
Proof. by rewrite in_fsetD in_fset1. Qed.

Definition in_fsetE := 
  (in_fset0, in_fset1, in_fsetU, in_fset1U, in_fsetI, in_fsetD, in_fsetD1).

Lemma fsetIC (A B : {fset K}) : A :&: B = B :&: A.
Proof. by apply/fsetP => a; rewrite !in_fsetI andbC. Qed.

Lemma fsetUC (A B : {fset K}) : A :|: B = B :|: A.
Proof. by apply/fsetP => a; rewrite !in_fsetU orbC. Qed.

Lemma fset0I A : fset0 :&: A = fset0.
Proof. by apply/fsetP => x; rewrite in_fsetI andFb. Qed.

Lemma fsetI0 A : A :&: fset0 = fset0.
Proof. by rewrite fsetIC fset0I. Qed.

Lemma fsetIA A B C : A :&: (B :&: C) = A :&: B :&: C.
Proof. by apply/fsetP=> x; rewrite !in_fsetI andbA. Qed.

Lemma fsetICA A B C : A :&: (B :&: C) = B :&: (A :&: C).
Proof. by rewrite !fsetIA (fsetIC A). Qed.

Lemma fsetIAC A B C : A :&: B :&: C = A :&: C :&: B.
Proof. by rewrite -!fsetIA (fsetIC B). Qed.

Lemma fsetIACA A B C D : (A :&: B) :&: (C :&: D) = (A :&: C) :&: (B :&: D).
Proof. by rewrite -!fsetIA (fsetICA B). Qed.

Lemma fsetIid A : A :&: A = A.
Proof. by apply/fsetP=> x; rewrite in_fsetI andbb. Qed.

Lemma fsetIIl A B C : A :&: B :&: C = (A :&: C) :&: (B :&: C).
Proof. by rewrite fsetIA !(fsetIAC _ C) -(fsetIA _ C) fsetIid. Qed.

Lemma fsetIIr A B C : A :&: (B :&: C) = (A :&: B) :&: (A :&: C).
Proof. by rewrite !(fsetIC A) fsetIIl. Qed.

(* distribute /cancel *)

Lemma fsetIUr A B C : A :&: (B :|: C) = (A :&: B) :|: (A :&: C).
Proof. by apply/fsetP=> x; rewrite !in_fsetE andb_orr. Qed.

Lemma fsetIUl A B C : (A :|: B) :&: C = (A :&: C) :|: (B :&: C).
Proof. by apply/fsetP=> x; rewrite !in_fsetE andb_orl. Qed.

Lemma fsetUIr A B C : A :|: (B :&: C) = (A :|: B) :&: (A :|: C).
Proof. by apply/fsetP=> x; rewrite !in_fsetE orb_andr. Qed.

Lemma fsetUIl A B C : (A :&: B) :|: C = (A :|: C) :&: (B :|: C).
Proof. by apply/fsetP=> x; rewrite !in_fsetE orb_andl. Qed.

Lemma fsetUK A B : (A :|: B) :&: A = A.
Proof. by apply/fsetP=> x; rewrite !in_fsetE orbK. Qed.

Lemma fsetKU A B : A :&: (B :|: A) = A.
Proof. by apply/fsetP=> x; rewrite !in_fsetE orKb. Qed.

Lemma fsetIK A B : (A :&: B) :|: A = A.
Proof. by apply/fsetP=> x; rewrite !in_fsetE andbK. Qed.

Lemma fsetKI A B : A :|: (B :&: A) = A.
Proof. by apply/fsetP=> x; rewrite !in_fsetE andKb. Qed.

(* subset *)

Lemma fsubsetP {A B} : reflect {subset A <= B} (A \fsubset B).
Proof.
apply: (iffP fset_eqP) => AsubB a; first by rewrite -AsubB in_fsetI => /andP[].
by rewrite in_fsetI; have [/AsubB|] := boolP (a \in A).
Qed.

Lemma fsetD_eq0 (A B : {fset K}) : (A :\: B == fset0) = (A \fsubset B).
Proof.
apply/fset_eqP/fsubsetP => sAB a.
  by move=> aA; apply: contraFT (sAB a); rewrite in_fsetD aA andbT.
by rewrite in_fsetD in_fset0 andbC; apply/negP => /andP [/sAB ->].
Qed.

Lemma fsubsetAA A : A \fsubset A. Proof. exact/fsubsetP. Qed.
Hint Resolve fsubsetAA.

Definition fincl A B (AsubB : A \fsubset B) (a : A) : B := 
  SeqSub ((fsubsetP AsubB) _ (ssvalP a)).

Definition fsub B A : {set B} := [set x : B | ssval x \in A].

Lemma fsubE A B (AsubB : A \fsubset B) : 
  fsub B A = [set fincl AsubB x | x in {: A}].
Proof.
apply/setP => x; rewrite in_set; apply/idP/imsetP => [|[[a aA] aA' ->]] //.
by move=> xA; exists (SeqSub xA)=> //; apply: val_inj.
Qed.

Lemma fincl_fsub A B (AsubB : A \fsubset B) (a : A) :
  fincl AsubB a \in fsub B A.
Proof. by rewrite inE /= ssvalP. Qed.

Lemma in_fsub B A (b : B) : (b \in fsub B A) = (ssval b \in A).
Proof. by rewrite inE. Qed.

Lemma subset_fsubE C A B : A \fsubset C -> B \fsubset C ->
   (fsub C A \subset fsub C B) = (A \fsubset B).
Proof.
move=> sAC sBC; apply/subsetP/fsubsetP => sAB a; last first.
  by rewrite !in_fsub => /sAB.
by move=> aA; have := sAB _ (fincl_fsub sAC (SeqSub aA)); rewrite in_fsub.
Qed.

Lemma fsubset_trans : transitive (@fsubset K).
Proof. by move=>??? s t ; apply/fsubsetP => a /(fsubsetP s) /(fsubsetP t). Qed.

Lemma subset_fsub A B C : A \fsubset B -> B \fsubset C ->
  fsub C A \subset fsub C B.
Proof. by move=> sAB sBC; rewrite subset_fsubE // (fsubset_trans sAB). Qed.

Lemma fsetIidPl {A B} : reflect (A :&: B = A) (A \fsubset B).
Proof. exact: eqP. Qed.

Lemma fsetIidPr {A B} : reflect (A :&: B = B) (B \fsubset A).
Proof. by rewrite fsetIC; apply: fsetIidPl. Qed.

Lemma fsubsetIidl A B : (A \fsubset A :&: B) = (A \fsubset B).
Proof.
by apply/fsubsetP/fsubsetP=> sAB a aA; have := sAB _ aA; rewrite !in_fsetI ?aA.
Qed.

Lemma fsubsetIidr A B : (B \fsubset A :&: B) = (B \fsubset A).
Proof. by rewrite fsetIC fsubsetIidl. Qed.

Lemma fsetUidPr A B : reflect (A :|: B = B) (A \fsubset B).
Proof.
apply: (iffP fsubsetP) => sAB; last by move=> a aA; rewrite -sAB in_fsetU aA.
by apply/fsetP => b; rewrite in_fsetU; have [/sAB|//] := boolP (_ \in _).
Qed.

Lemma fsetUidPl A B : reflect (A :|: B = A) (B \fsubset A).
Proof. by rewrite fsetUC; apply/fsetUidPr. Qed.

Lemma fsubsetUl A B : A \fsubset A :|: B.
Proof. by apply/fsubsetP => a; rewrite in_fsetU => ->. Qed.
Hint Resolve fsubsetUl.

Lemma fsubsetUr A B : B \fsubset A :|: B.
Proof. by rewrite fsetUC. Qed.
Hint Resolve fsubsetUr.

Lemma fsubsetU1 x A : A \fsubset x |: A.
Proof. by rewrite fsubsetUr. Qed.
Hint Resolve fsubsetU1.

Lemma fsubsetU A B C : (A \fsubset B) || (A \fsubset C) -> A \fsubset B :|: C.
Proof. by move=> /orP [] /fsubset_trans ->. Qed.

Lemma fincl_inj A B (AsubB : A \fsubset B) : injective (fincl AsubB).
Proof. by move=> a b [eq_ab]; apply: val_inj. Qed.
Hint Resolve fincl_inj.

Lemma fsub_inj B : {in [pred A | A \fsubset B] &, injective (fsub B)}.
Proof.
move=> A A'; rewrite -!topredE /= => sAB sA'B /setP eqAA'; apply/fsetP => a.
apply/idP/idP => mem_a.
  have := eqAA' (fincl sAB (SeqSub mem_a)).
  by rewrite !in_fsub // => <-.
have := eqAA' (fincl sA'B (SeqSub mem_a)).
by rewrite !in_fsub // => ->.
Qed.
Hint Resolve fsub_inj.

Lemma eqEfsubset A B : (A == B) = (A \fsubset B) && (B \fsubset A).
Proof.
apply/eqP/andP => [-> //|[/fsubsetP AB /fsubsetP BA]].
by apply/fsetP=> x; apply/idP/idP=> [/AB|/BA].
Qed.

Lemma subEfproper A B : A \fsubset B = (A == B) || (A \fproper B).
Proof. by rewrite eqEfsubset -andb_orr orbN andbT. Qed.

Lemma fproper_sub A B : A \fproper B -> A \fsubset B.
Proof. by rewrite subEfproper orbC => ->. Qed.

Lemma eqVfproper A B : A \fsubset B -> A = B \/ A \fproper B.
Proof. by rewrite subEfproper => /predU1P. Qed.

Lemma fproperEneq A B : A \fproper B = (A != B) && (A \fsubset B).
Proof. by rewrite andbC eqEfsubset negb_and andb_orr andbN. Qed.

Lemma fproper_neq A B : A \fproper B -> A != B.
Proof. by rewrite fproperEneq; case/andP. Qed.

Lemma eqEfproper A B : (A == B) = (A \fsubset B) && ~~ (A \fproper B).
Proof. by rewrite negb_and negbK andb_orr andbN eqEfsubset. Qed.

Lemma card_fsub B A : A \fsubset B -> #|fsub B A| = #|{: A}|.
Proof. by move=> sAB; rewrite fsubE card_imset //; apply: fincl_inj. Qed.

Lemma eqEfcard A B : (A == B) = (A \fsubset B) &&
  (#|{: B}| <= #|{: A}|)%N.
Proof.
rewrite -(inj_in_eq (@fsub_inj (A :|: B))) -?topredE //=.
by rewrite eqEcard !(@subset_fsubE (A :|: B)) ?(@card_fsub (A :|: B)).
Qed.

Lemma fproperEcard A B : 
  (A \fproper B) = (A \fsubset B) && (#|{: A}| < #|{: B}|)%N.
Proof. by rewrite fproperEneq ltnNge andbC eqEfcard; case: (A \fsubset B). Qed.

Lemma fsubset_leqif_cards A B : A \fsubset B -> (#|{: A}| <= #|{: B}| ?= iff (A == B))%N.
Proof.
rewrite -!(@card_fsub (A :|: B)) // -(@subset_fsubE (A :|: B)) //.
by move=> /subset_leqif_cards; rewrite (inj_in_eq (@fsub_inj _)) -?topredE /=.
Qed.

Lemma fsub0set A : fset0 \fsubset A.
Proof. by apply/fsubsetP=> x; rewrite inE. Qed.
Hint Resolve fsub0set.

Lemma fsubset0 A : (A \fsubset fset0) = (A == fset0).
Proof. by rewrite eqEfsubset fsub0set andbT. Qed.

Lemma fproper0 A : (fset0 \fproper A) = (A != fset0).
Proof. by rewrite /fproper fsub0set fsubset0. Qed.

Lemma fproperE A B : (A \fproper B) = (A \fsubset B) && ~~ (B \fsubset A).
Proof. by []. Qed.

Lemma fsubEproper A B : (A \fsubset B) = (A == B) || (A \fproper B).
Proof. by rewrite fproperEneq; case: eqP => //= ->; apply: fsubsetAA. Qed.

Lemma fsubset_leq_card A B : A \fsubset B -> (#|{: A}| <= #|{: B}|)%N.
Proof. by move=> /fsubset_leqif_cards ->. Qed.

Lemma fproper_ltn_card A B : A \fproper B -> (#|{: A}| < #|{: B}|)%N.
Proof. by rewrite fproperEcard => /andP []. Qed.

Lemma fsubset_cardP A B : #|{: A}| = #|{: B}| ->
  reflect (A =i B) (A \fsubset B).
Proof.
move=> eq_cardAB; apply: (iffP idP) => [/eqVfproper [->//|]|/fsetP -> //].
by rewrite fproperEcard eq_cardAB ltnn andbF.
Qed.

Lemma fproper_sub_trans B A C : A \fproper B -> B \fsubset C -> A \fproper C.
Proof.
rewrite !fproperEcard => /andP [sAB lt_AB] sBC.
by rewrite (fsubset_trans sAB) //= (leq_trans lt_AB) // fsubset_leq_card.
Qed.

Lemma fsub_proper_trans B A C :
  A \fsubset B -> B \fproper C -> A \fproper C.
Proof.
rewrite !fproperEcard => sAB /andP [sBC lt_BC].
by rewrite (fsubset_trans sAB) //= (leq_ltn_trans _ lt_BC) // fsubset_leq_card.
Qed.

Lemma fsubset_neq0 A B : A \fsubset B -> A != fset0 -> B != fset0.
Proof. by rewrite -!fproper0 => sAB /fproper_sub_trans->. Qed.

(* fsub is a morphism *)

Lemma fsub0 A : fsub A fset0 = set0 :> {set A}.
Proof. by apply/setP => x; rewrite in_fsub. Qed.

Lemma fsub1 A a (aA : a \in A) : fsub A [fset a] = [set SeqSub aA] :> {set A}.
Proof. by apply/setP=> x; rewrite in_fsub in_set1 in_fset1; congr eq_op. Qed.

Lemma fsubU C A B : fsub C (A :|: B) = (fsub C A :|: fsub C B)%SET.
Proof. by apply/setP => x; rewrite !(in_fsub, in_setU, in_fsetU). Qed.

Lemma fsubI C A B : fsub C (A :&: B) = (fsub C A :&: fsub C B)%SET.
Proof. by apply/setP => x; rewrite !(in_fsub, in_setI, in_fsetI). Qed.

Lemma fsubD C A B : fsub C (A :\: B) = (fsub C A :\: fsub C B)%SET.
Proof. by apply/setP => x; rewrite !(in_fsub, in_setD, in_fsetD) andbC. Qed.

Lemma fsubD1 C A b (bC : b \in C) : fsub C (A :\ b) = (fsub C A :\ SeqSub bC)%SET.
Proof. by rewrite fsubD fsub1. Qed.

Lemma fsub_eq0 A B : A \fsubset B -> (fsub B A == set0) = (A == fset0).
Proof.
by move=> sAB; rewrite -fsub0 (inj_in_eq (@fsub_inj _)) -?topredE /=.
Qed.

Lemma fset_0Vmem A : (A = fset0) + {x : K | x \in A}.
Proof.
have [|[x mem_x]] := set_0Vmem (fsub A A); last first.
  by right; exists (ssval x); rewrite in_fsub // in mem_x.
by move=> /eqP; rewrite fsub_eq0 // => /eqP; left.
Qed.

Lemma fset1P x a : reflect (x = a) (x \in [fset a]).
Proof. by rewrite in_fset1; exact: eqP. Qed.

Lemma fset11 x : x \in [fset x].
Proof. by rewrite in_fset1. Qed.

Lemma fset1_inj : injective (@fset1 K).
Proof. by move=> a b eqsab; apply/fset1P; rewrite -eqsab fset11. Qed.

Lemma fset1UP x a B : reflect (x = a \/ x \in B) (x \in a |: B).
Proof. by rewrite !in_fset1U; exact: predU1P. Qed.

Lemma fset_cons a s : fset (a :: s) = a |: (fset s).
Proof. by apply/fsetP=> x; rewrite in_fset1U !in_fset. Qed.

Lemma fset1U1 x B : x \in x |: B.
Proof. by rewrite in_fset1U eqxx. Qed.

Lemma fset1Ur x a B : x \in B -> x \in a |: B.
Proof. by move=> Bx; rewrite in_fset1U predU1r. Qed.

(* We need separate lemmas for the explicit enumerations since they *)
(* associate on the left.                                           *)
Lemma fsetU1l x A b : x \in A -> x \in A :|: [fset b].
Proof. by move=> Ax; rewrite !in_fsetU Ax. Qed.

Lemma fsetU1r A b : b \in A :|: [fset b].
Proof. by rewrite in_fsetU in_fset1 eqxx orbT. Qed.

Lemma fsetD1P x A b : reflect (x != b /\ x \in A) (x \in A :\ b).
Proof. by rewrite in_fsetD1; exact: andP. Qed.

Lemma fsetD11 b A : (b \in A :\ b) = false.
Proof. by rewrite in_fsetD1 eqxx. Qed.

Lemma fsetD1K a A : a \in A -> a |: (A :\ a) = A.
Proof.
by move=> Aa; apply/fsetP=> x; rewrite !in_fsetE; case: eqP => // ->.
Qed.

Lemma fsetU1K a B : a \notin B -> (a |: B) :\ a = B.
Proof.
by move/negPf=> nBa; apply/fsetP=> x; rewrite !in_fsetE; case: eqP => // ->.
Qed.

Lemma fset2P x a b : reflect (x = a \/ x = b) (x \in [fset a; b]).
Proof. by rewrite !in_fsetE; apply: (iffP orP) => [] [] /eqP; intuition. Qed.

Lemma in_fset2 x a b : (x \in [fset a; b]) = (x == a) || (x == b).
Proof. by rewrite !in_fsetU !in_fset1. Qed.

Lemma set21 a b : a \in [fset a; b]. Proof. by rewrite fset1U1. Qed.

Lemma set22 a b : b \in [fset a; b]. Proof. by rewrite in_fset2 eqxx orbT. Qed.

Lemma fsetUP x A B : reflect (x \in A \/ x \in B) (x \in A :|: B).
Proof. by rewrite !in_fsetU; exact: orP. Qed.

Lemma fsetUS A B C : A \fsubset B -> C :|: A \fsubset C :|: B.
Proof.
move=> sAB; apply/fsubsetP=> x; rewrite !in_fsetU.
by case: (x \in C) => //; exact: (fsubsetP sAB).
Qed.

Lemma fsetSU A B C : A \fsubset B -> A :|: C \fsubset B :|: C.
Proof. by move=> sAB; rewrite -!(fsetUC C) fsetUS. Qed.

Lemma fsetUSS A B C D : A \fsubset C -> B \fsubset D -> A :|: B \fsubset C :|: D.
Proof. by move=> /(fsetSU B) /fsubset_trans sAC /(fsetUS C)/sAC. Qed.

Lemma fset0U A : fset0 :|: A = A.
Proof. by apply/fsetP => x; rewrite !in_fsetU orFb. Qed.

Lemma fsetU0 A : A :|: fset0 = A.
Proof. by rewrite fsetUC fset0U. Qed.

Lemma fsetUA A B C : A :|: (B :|: C) = A :|: B :|: C.
Proof. by apply/fsetP => x; rewrite !in_fsetU orbA. Qed.

Lemma fsetUCA A B C : A :|: (B :|: C) = B :|: (A :|: C).
Proof. by rewrite !fsetUA (fsetUC B). Qed.

Lemma fsetUAC A B C : A :|: B :|: C = A :|: C :|: B.
Proof. by rewrite -!fsetUA (fsetUC B). Qed.

Lemma fsetUACA A B C D : (A :|: B) :|: (C :|: D) = (A :|: C) :|: (B :|: D).
Proof. by rewrite -!fsetUA (fsetUCA B). Qed.

Lemma fsetUid A : A :|: A = A.
Proof. by apply/fsetP=> x; rewrite in_fsetU orbb. Qed.

Lemma fsetUUl A B C : A :|: B :|: C = (A :|: C) :|: (B :|: C).
Proof. by rewrite fsetUA !(fsetUAC _ C) -(fsetUA _ C) fsetUid. Qed.

Lemma setUUr A B C : A :|: (B :|: C) = (A :|: B) :|: (A :|: C).
Proof. by rewrite !(fsetUC A) fsetUUl. Qed.

(* intersection *)

Lemma fsetIP x A B : reflect (x \in A /\ x \in B) (x \in A :&: B).
Proof. by rewrite in_fsetI; apply: andP. Qed.

Lemma fsetIS A B C : A \fsubset B -> C :&: A \fsubset C :&: B.
Proof.
move=> sAB; apply/fsubsetP=> x; rewrite !in_fsetI.
by case: (x \in C) => //; exact: (fsubsetP sAB).
Qed.

Lemma fsetSI A B C : A \fsubset B -> A :&: C \fsubset B :&: C.
Proof. by move=> sAB; rewrite -!(fsetIC C) fsetIS. Qed.

Lemma fsetISS A B C D : A \fsubset C -> B \fsubset D -> A :&: B \fsubset C :&: D.
Proof. by move=> /(fsetSI B) /fsubset_trans sAC /(fsetIS C) /sAC. Qed.

(* difference *)

Lemma fsetDP A B x : reflect (x \in A /\ x \notin B) (x \in A :\: B).
Proof. by rewrite in_fsetD andbC; apply: andP. Qed.

Lemma fsetSD A B C : A \fsubset B -> A :\: C \fsubset B :\: C.
Proof. 
move=> sAB; apply/fsubsetP=> x; rewrite !in_fsetD.
by case: (x \in C) => //; exact: (fsubsetP sAB).
Qed.

Lemma fsetDS A B C : A \fsubset B -> C :\: B \fsubset C :\: A.
Proof.
move=> sAB; apply/fsubsetP=> x; rewrite !in_fsetD ![_ && (_ \in _)]andbC.
by case: (x \in C) => //; apply: contra; exact: (fsubsetP sAB).
Qed.

Lemma fsetDSS A B C D : A \fsubset C -> D \fsubset B -> A :\: B \fsubset C :\: D.
Proof. by move=> /(fsetSD B) /fsubset_trans sAC /(fsetDS C) /sAC. Qed.

Lemma fsetD0 A : A :\: fset0 = A.
Proof. by apply/fsetP=> x; rewrite !in_fsetE. Qed.

Lemma fset0D A : fset0 :\: A = fset0.
Proof. by apply/fsetP=> x; rewrite !in_fsetE andbF. Qed.

Lemma fsetDv A : A :\: A = fset0.
Proof. by apply/fsetP=> x; rewrite !in_fsetD andNb. Qed.

Lemma fsetID A B : A :&: B :|: A :\: B = A.
Proof. by apply/fsetP=> x; rewrite !in_fsetE; do ?case: (_ \in _). Qed.

Lemma fsetDUl A B C : (A :|: B) :\: C = (A :\: C) :|: (B :\: C).
Proof. by apply/fsetP=> x; rewrite !in_fsetE; do ?case: (_ \in _). Qed.

Lemma fsetDUr A B C : A :\: (B :|: C) = (A :\: B) :&: (A :\: C).
Proof. by apply/fsetP=> x; rewrite !in_fsetE; do ?case: (_ \in _). Qed.

Lemma fsetDIl A B C : (A :&: B) :\: C = (A :\: C) :&: (B :\: C).
Proof. by apply/fsetP=> x; rewrite !in_fsetE; do ?case: (_ \in _). Qed.

Lemma fsetIDA A B C : A :&: (B :\: C) = (A :&: B) :\: C.
Proof. by apply/fsetP=> x; rewrite !in_fsetE; do ?case: (_ \in _). Qed.

Lemma fsetIDAC A B C : (A :\: B) :&: C = (A :&: C) :\: B.
Proof. by apply/fsetP=> x; rewrite !in_fsetE; do ?case: (_ \in _). Qed.

Lemma fsetDIr A B C : A :\: (B :&: C) = (A :\: B) :|: (A :\: C).
Proof. by apply/fsetP=> x; rewrite !in_fsetE; do ?case: (_ \in _). Qed.

Lemma fsetDDl A B C : (A :\: B) :\: C = A :\: (B :|: C).
Proof. by apply/fsetP=> x; rewrite !in_fsetE; do ?case: (_ \in _). Qed.

Lemma fsetDDr A B C : A :\: (B :\: C) = (A :\: B) :|: (A :&: C).
Proof. by apply/fsetP=> x; rewrite !in_fsetE; do ?case: (_ \in _). Qed.


(* other inclusions *)

Lemma fsubsetIl A B : A :&: B \fsubset A.
Proof. by apply/fsubsetP=> x; rewrite in_fsetE => /andP []. Qed.

Lemma fsubsetIr A B : A :&: B \fsubset B.
Proof. by apply/fsubsetP=> x; rewrite in_fsetE => /andP []. Qed.

Lemma fsubsetDl A B : A :\: B \fsubset A.
Proof. by apply/fsubsetP=> x; rewrite in_fsetE => /andP []. Qed.

Lemma fsubD1set A x : A :\ x \fsubset A.
Proof. by rewrite fsubsetDl. Qed.

Hint Resolve fsubsetIl fsubsetIr fsubsetDl fsubD1set.

(* cardinal lemmas for fsets *)

Lemma cardfs0 : #|{: @fset0 K}| = 0.
Proof. by rewrite -(@card_fsub fset0) // fsub0 cards0. Qed.

Lemma cardfs_eq0 A : (#|{: A}| == 0) = (A == fset0).
Proof. by rewrite -(@card_fsub A) // cards_eq0 fsub_eq0. Qed.

Lemma cardfs0_eq A : #|{: A}| = 0 -> A = fset0.
Proof. by move=> /eqP; rewrite cardfs_eq0 => /eqP. Qed.

Lemma fset0Pn A : reflect (exists x, x \in A) (A != fset0).
Proof.
rewrite -cardfs_eq0; apply: (equivP existsP).
by split=> [] [a aP]; [exists (ssval a); apply: ssvalP|exists (SeqSub aP)].
Qed.

Lemma cardfs_gt0 A : (0 < #|{: A}|)%N = (A != fset0).
Proof. by rewrite lt0n cardfs_eq0. Qed.

Lemma cardfsE s : #|{: fset s}| = size (undup s).
Proof.
rewrite cardT enumT unlock /= undup_id ?pmap_sub_uniq ?sort_keys_uniq //.
by rewrite size_pmap_sub (@eq_in_count _ _ predT) ?count_predT ?size_sort_keys.
Qed.

Lemma cardfs1 x : #|{: [fset x]}| = 1.
Proof. by rewrite cardfsE undup_id. Qed.

Lemma cardfsUI A B : #|{: A :|: B}| + #|{: A :&: B}| = #|{: A}| + #|{: B}|.
Proof. 
rewrite -!(@card_fsub (A :|: B)) ?(fsubset_trans (fsubsetIl _ _)) //.
by rewrite fsubU fsubI cardsUI.
Qed.

Lemma cardfsU A B : #|{: A :|: B}| = (#|{: A}| + #|{: B}| - #|{: A :&: B}|)%N.
Proof. by rewrite -cardfsUI addnK. Qed.

Lemma cardfsI A B : #|{: A :&: B}| = (#|{: A}| + #|{: B}| - #|{: A :|: B}|)%N.
Proof. by rewrite  -cardfsUI addKn. Qed.

Lemma cardfsID B A : #|{: A :&: B}| + #|{: A :\: B}| = #|{: A}|.
Proof. by rewrite -!(@card_fsub A) // fsubI fsubD cardsID. Qed.

Lemma cardfsD A B : #|{: A :\: B}| = (#|{: A}| - #|{: A :&: B}|)%N.
Proof. by rewrite -(cardfsID B A) addKn. Qed.

Lemma mem_fset1U a A : a \in A -> a |: A = A.
Proof.
move=> aA; apply/fsetP => x; rewrite !in_fsetE orbC.
by have [//|/=] := boolP (_ \in A); apply: contraNF => /eqP ->.
Qed.

Lemma mem_fsetD1 a A : a \notin A -> A :\ a = A.
Proof.
move=> aA; apply/fsetP => x; rewrite !in_fsetE andbC.
by have [/= xA|//] := boolP (_ \in A); apply: contraNneq aA => <-.
Qed.

Lemma fsetI1 a A : A :&: [fset a] = if a \in A then [fset a] else fset0.
Proof.
apply/fsetP => x; rewrite (fun_if (fun X => _ \in X)) !in_fsetE.
by have [[->|?] []] := (altP (x =P a), boolP (a \in A)); rewrite ?andbF.
Qed.

Lemma cardfsU1 a A : #|{: a |: A}| = (a \notin A) + #|{: A}|.
Proof.
have [aA|aNA] := boolP (a \in A); first by rewrite mem_fset1U.
rewrite cardfsU -addnBA ?fsubset_leq_card // fsetIC -cardfsD.
by rewrite mem_fsetD1 // cardfs1.
Qed.

Lemma cardfs2 a b : #|{: [fset a; b]}| = (a != b).+1.
Proof. by rewrite !cardfsU1 cardfs1 addn1 in_fset in_cons orbF. Qed.

Lemma cardfsD1 a A : #|{: A}| = (a \in A) + #|{: A :\ a}|.
Proof.
rewrite -(cardfsID [fset a]) fsetI1 (fun_if (fun A => #|{: A}|)).
by rewrite cardfs0 cardfs1; case: (_ \in _).
Qed.

(* other inclusions *)

Lemma fsub1set A x : ([fset x] \fsubset A) = (x \in A).
Proof.
rewrite -(@subset_fsubE (x |: A)) // fsub1 ?fset1U1 // => xxA.
by rewrite sub1set in_fsub.
Qed.

Lemma cardfs1P A : reflect (exists x, A = [fset x]) (#|{: A}| == 1).
Proof.
apply: (iffP idP) => [|[x ->]]; last by rewrite cardfs1.
rewrite eq_sym eqn_leq cardfs_gt0=> /andP[/fset0Pn[x Ax] leA1].
by exists x; apply/eqP; rewrite eq_sym eqEfcard fsub1set cardfs1 leA1 Ax.
Qed.

Lemma fsubset1 A x : (A \fsubset [fset x]) = (A == [fset x]) || (A == fset0).
Proof.
rewrite eqEfcard cardfs1 -cardfs_eq0 orbC andbC.
by case: posnP => // A0; rewrite (cardfs0_eq A0) fsub0set.
Qed.

Implicit Arguments fsetIidPl [A B].

Lemma cardfsDS A B : B \fsubset A -> #|{: A :\: B}| = (#|{: A}| - #|{: B}|)%N.
Proof. by rewrite cardfsD => /fsetIidPr->. Qed.

Lemma fsubIset A B C : (B \fsubset A) || (C \fsubset A) -> (B :&: C \fsubset A).
Proof. by case/orP; apply: fsubset_trans; rewrite (fsubsetIl, fsubsetIr). Qed.

Lemma fsubsetI A B C : (A \fsubset B :&: C) = (A \fsubset B) && (A \fsubset C).
Proof.
rewrite !(sameP fsetIidPl eqP) fsetIA; have [-> //| ] := altP (A :&: B =P A).
by apply: contraNF => /eqP <-; rewrite -fsetIA -fsetIIl fsetIAC.
Qed.

Lemma fsubsetIP A B C : reflect (A \fsubset B /\ A \fsubset C) (A \fsubset B :&: C).
Proof. by rewrite fsubsetI; exact: andP. Qed.

Lemma fsubUset A B C : (B :|: C \fsubset A) = (B \fsubset A) && (C \fsubset A).
Proof.
apply/idP/idP => [subA|/andP [AB CA]]; last by rewrite -[A]fsetUid fsetUSS.
by rewrite !(fsubset_trans _ subA).
Qed.
 
Lemma fsubUsetP A B C : reflect (A \fsubset C /\ B \fsubset C) (A :|: B \fsubset C).
Proof. by rewrite fsubUset; exact: andP. Qed.

Lemma fsubDset A B C : (A :\: B \fsubset C) = (A \fsubset B :|: C).
Proof.
apply/fsubsetP/fsubsetP=> sABC x; rewrite !in_fsetE.
  by case Bx: (x \in B) => // Ax; rewrite sABC ?in_fsetD ?Bx.
by case Bx: (x \in B) => //; move/sABC; rewrite in_fsetE Bx.
Qed.

Lemma fsetU_eq0 A B : (A :|: B == fset0) = (A == fset0) && (B == fset0).
Proof. by rewrite -!fsubset0 fsubUset. Qed.

Lemma setD_eq0 A B : (A :\: B == fset0) = (A \fsubset B).
Proof. by rewrite -fsubset0 fsubDset fsetU0. Qed.

Lemma fsubsetD1 A B x : (A \fsubset B :\ x) = (A \fsubset B) && (x \notin A).
Proof.
do !rewrite -(@subset_fsubE (x |: A :|: B)) ?fsubDset ?fsetUA // 1?fsetUAC //.
rewrite fsubD1 => [|mem_x]; first by rewrite -fsetUA fset1U1.
by rewrite subsetD1 // in_fsub.
Qed.

Lemma fsubsetD1P A B x : reflect (A \fsubset B /\ x \notin A) (A \fsubset B :\ x).
Proof. by rewrite fsubsetD1; exact: andP. Qed.

Lemma fsubsetPn A B : reflect (exists2 x, x \in A & x \notin B) (~~ (A \fsubset B)).
Proof.
 rewrite -fsetD_eq0; apply: (iffP (fset0Pn _)) => [[x]|[x xA xNB]].
  by rewrite in_fsetE => /andP[]; exists x.
by exists x; rewrite in_fsetE xA xNB.
Qed.

Lemma fproperD1 A x : x \in A -> A :\ x \fproper A.
Proof.
move=> Ax; rewrite fproperE fsubsetDl; apply/fsubsetPn; exists x=> //.
by rewrite in_fsetD1 Ax eqxx.
Qed.

Lemma fproperIr A B : ~~ (B \fsubset A) -> A :&: B \fproper B.
Proof. by move=> nsAB; rewrite fproperE fsubsetIr fsubsetI negb_and nsAB. Qed.

Lemma fproperIl A B : ~~ (A \fsubset B) -> A :&: B \fproper A.
Proof. by move=> nsBA; rewrite fproperE fsubsetIl fsubsetI negb_and nsBA orbT. Qed.

Lemma fproperUr A B : ~~ (A \fsubset B) ->  B \fproper A :|: B.
Proof. by rewrite fproperE fsubsetUr fsubUset fsubsetAA /= andbT. Qed.

Lemma fproperUl A B : ~~ (B \fsubset A) ->  A \fproper A :|: B.
Proof. by move=> not_sBA; rewrite fsetUC fproperUr. Qed.

Lemma fproper1set A x : ([fset x] \fproper A) -> (x \in A).
Proof. by move/fproper_sub; rewrite fsub1set. Qed.

Lemma fproperIset A B C : (B \fproper A) || (C \fproper A) -> (B :&: C \fproper A).
Proof. by case/orP; apply: fsub_proper_trans; rewrite (fsubsetIl, fsubsetIr). Qed.

Lemma fproperI A B C : (A \fproper B :&: C) -> (A \fproper B) && (A \fproper C).
Proof.
move=> pAI; apply/andP.
by split; apply: (fproper_sub_trans pAI); rewrite (fsubsetIl, fsubsetIr).
Qed.

Lemma fproperU A B C : (B :|: C \fproper A) -> (B \fproper A) && (C \fproper A).
Proof.
move=> pUA; apply/andP.
by split; apply: fsub_proper_trans pUA; rewrite (fsubsetUr, fsubsetUl).
Qed.

Lemma val_in_FSet A (X : {set A}) (k : A) : (val k \in FSet X) = (k \in X).
Proof.
by rewrite inE /= sort_keysE mem_map ?mem_enum => //= x y ?; apply: val_inj.
Qed.

Lemma FSet_sub A (X : {set A}) : FSet X \fsubset A.
Proof.
apply/fsubsetP => k; rewrite inE /= sort_keysE => /mapP [/= x].
by rewrite mem_enum => _ ->; apply: valP.
Qed.

Lemma in_FSet A (X : {set A}) (k : K) (kA : k \in A) :
  (k \in FSet X) = (SeqSub kA \in X).
Proof. by rewrite -val_in_FSet. Qed.

(* :TODO: rename *)
Lemma in_FSetE A (X : {set A}) (k : K) :
  k \in FSet X -> {kA : k \in A & SeqSub kA \in X}.
Proof.
rewrite inE sort_keysE => /mapP [/= x x_in_X ->].
exists (valP x); rewrite mem_enum in x_in_X.
by set y := (y in y \in X); suff <- : x = y by []; apply: val_inj.
Qed.

Lemma fsubK A B : A \fsubset B -> FSet (fsub B A) = A.
Proof.
move=> AsubB; apply/fsetP => k /=; symmetry.
have [kB|kNB] := (boolP (k \in B)); first by rewrite in_FSet in_fsub.
rewrite (contraNF (fsubsetP (FSet_sub _) _)) //.
by apply: contraNF kNB; apply: fsubsetP.
Qed.

Lemma FSetK A (X : {set A}) : fsub A (FSet X) = X.
Proof. by apply/setP => x; rewrite in_fsub val_in_FSet. Qed.

End Theory.

Section DefMap.
Variables (K : keyType) (V : Type).

Record finMap : Type := FinMap {
  domf : {fset K};
  ffun_of_fmap :> {ffun domf -> V}
}.

Definition finmap_of (_ : phant (K -> V)) := finMap.
End DefMap.

Notation "{fmap T }" := (@finmap_of _ _ (Phant T)) : type_scope.

Definition pred_of_finmap (K : keyType) (V : Type)
  (f : {fmap K -> V}) : pred K := mem (domf f).
Canonical finMapPredType (K : keyType) (V : Type) :=
  Eval hnf in mkPredType (@pred_of_finmap K V).

Delimit Scope fmap_scope with fmap.
Local Open Scope fmap_scope.
Notation "f .[ kf ]" := (f (SeqSub kf)) : fmap_scope.

Section OpsMap.

Variables (K : keyType).

Definition nilf V : {fmap K -> V} := FinMap (ffun0 _ (cardfs0 K)).

Definition fnd V (f : {fmap K -> V}) := fun k =>
 if (k \in f) =P true is ReflectT k_in_f then some (f.[k_in_f]) else None.

Inductive fnd_spec V (f : {fmap K -> V}) k : bool -> option V -> Type :=
| FndIn  (kf : k \in f) : fnd_spec f k true (some (f.[kf]))
| FndOut (kNf : k \notin f) : fnd_spec f k false None.

Definition setf V (f : {fmap K -> V}) (k0 : K) (v0 : V) : {fmap K -> V} :=
  FinMap [ffun k : (k0 |: domf f) => if val k == k0 :> K then v0 
                                       else odflt v0 (fnd f (val k))].

  
End OpsMap.

Prenex Implicits fnd setf.
Arguments nilf {K V}.
Arguments setf : simpl never.
Arguments fnd : simpl never.

Notation "x .[ k <- v ]" := (setf x k v) : fmap_scope.
Notation "f .[? k ]" := (fnd f k) : fmap_scope.

Section MapTheory.

Variables (K : keyType).

Lemma fndP V (f : {fmap K -> V}) k : fnd_spec f k (k \in f) (f.[? k]).
Proof.
rewrite /fnd; case: eqP => [kf|/negP kNf]; first by rewrite kf; constructor.
by rewrite (negPf kNf); constructor.
Qed.

Lemma fndSome V (f : {fmap K -> V}) (k : K) : f.[? k] = (k \in f) :> bool.
Proof. by case: fndP. Qed.

Lemma not_fnd V (f : {fmap K -> V}) (k : K) : k \notin f -> fnd f k = None.
Proof. by case: fndP. Qed.

Lemma getfE V (A : {fset K}) (f : {ffun A -> V}) (k : A)
      (kf : val k \in A) : f.[kf] = f k :> V.
Proof. by congr (_ _); apply: val_inj. Qed.

Lemma in_fnd V  (f : {fmap K -> V}) (k : K)
      (kf : k \in f) : f.[? k] = Some f.[kf].
Proof.
have := kf; case: fndP => // kf' _.
by congr (Some f.[_]); apply: bool_irrelevance.
Qed.

Lemma getfP V (f g : {fmap K -> V}) :
  domf f = domf g ->
  (forall k (kMf : k \in f) (kMg : k \in g), f.[kMf] = g.[kMg]) ->
  f = g.
Proof.
move: f g => [kf f] [kg g] /= eq_kfg; case: _ / eq_kfg in g * => {kg}.
move=> eq_fg; congr FinMap; apply/ffunP => /= x.
by do [rewrite -!getfE; do ?exact: valP] => *.
Qed.

Lemma fmap_fndP V (f g : {fmap K -> V}) : fnd f =1 fnd g -> f = g.
Proof.
move=> fnd_fg; apply: getfP => [|k kMf kMg].
  by apply/fsetP => x; rewrite -!fndSome fnd_fg.
by apply: Some_inj; rewrite -!in_fnd.
Qed.

Lemma mem_setf V (f : {fmap K -> V}) (k0 : K) (v0 : V) :
  f.[k0 <- v0] =i predU1 k0 (mem f).
Proof. by move=> k; rewrite !in_fsetE !inE. Qed.

Lemma fnd_setf_in V (f : {fmap K -> V}) k0 v0 (x : domf f.[k0 <- v0]) :
  val x != k0 -> val x \in f.
Proof. by have := valP x; rewrite mem_setf inE; case: eqP. Qed.

Lemma setfK V (f : {fmap K -> V}) k0 v0 (x : domf f.[k0 <- v0]):
   f.[k0 <- v0] x = if eqVneq (val x) k0 is right xNk0
                    then f.[fnd_setf_in xNk0] else v0.
Proof.
case: eqVneq => /= [|xNk0]; rewrite ?ffunE; first by move->; rewrite eqxx.
rewrite (negPf xNk0) in_fnd ?fnd_setf_in //= => xf.
by congr f.[_]; apply: bool_irrelevance.
Qed.

Lemma fnd_setf V (f : {fmap K -> V}) k0 v0 k :
   f.[k0 <- v0].[? k] = if k == k0 then Some v0 else f.[? k].
Proof.
case: fndP => [ksf|]; last first.
  by rewrite mem_setf inE negb_or => /andP [/negPf ->]; case: fndP.
rewrite setfK; case: eqVneq => //= [->|kNk0]; first by rewrite eqxx.
have kf := @fnd_setf_in _ _ _ _ (SeqSub ksf) kNk0.
rewrite (negPf kNk0); case: fndP kf => // kf' _.
by congr (Some f.[_]); apply: bool_irrelevance.
Qed.

Lemma fmap_nil V (f : {fmap K -> V}) : domf f = fset0 -> f = nilf.
Proof. by move=> kf0; apply: getfP. Qed.


Lemma getf_setf V (f : {fmap K -> V}) (k : K) (v : V) (kf' : k \in _) :
   f.[k <- v].[kf'] = v.
Proof. by apply: Some_inj; rewrite -in_fnd fnd_setf eqxx. Qed.

Lemma setfNK V (f : {fmap K -> V}) (k k' : K) (v : V)
      (k'f : k' \in _) (k'f' : k' \in _):
   f.[k <- v].[k'f'] = if k' == k then v else f.[k'f].
Proof. by apply: Some_inj; rewrite -in_fnd !fnd_setf in_fnd; case: ifP. Qed.

End MapTheory.

Section Ops2.

Variable K : keyType.

Lemma reducef_subproof V (f : {fmap K -> option V}) 
      (X := FSet [set x : domf f | f x])
      (x : X) (x' := (SeqSub (fsubsetP (FSet_sub _) _ (valP x)))) : f x'.
Proof.
suff : val x' \in X by rewrite val_in_FSet inE.
by have -> : val x' = val x by []; last apply: valP.
Qed.

Definition reducef V (f : {fmap K -> option V}) : {fmap K -> V} :=
  FinMap [ffun x => oextract (@reducef_subproof V f x)].

Definition filterf V (f : {fmap K -> V}) (P : pred K) :=
  reducef (FinMap [ffun x : domf f =>
                   if P (val x) then Some (f x) else None]).

Definition remf V (f : {fmap K -> V}) k := filterf f (predC1 k).

Arguments reducef : simpl never.
Arguments filterf : simpl never.
Arguments remf : simpl never.
Notation "x .[~ k ]" := (remf x k) : fmap_scope.

Definition ojoin T (x : option (option T)) :=
  if x is Some y then y else None.

Lemma Some_oextract T (x : option T) (x_ex : x) : Some (oextract x_ex) = x.
Proof. by case: x x_ex. Qed.

Lemma Some_ojoin T (x : option (option T)) : x -> Some (ojoin x) = x.
Proof. by case : x. Qed.

Lemma ojoinT T (x : option (option T)) : ojoin x -> x.
Proof. by case: x. Qed.

(* Lemma fnd_reducef  V (f : {fmap K -> option V}) k : *)
(*   (reducef f).[? k] = ojoin f.[? k]. *)
(* Proof. *)
(* case: fndP => [kf|kNf]; last first. *)
(*   case: fndP. *)
(*   rewrite  *)

Lemma mem_reducef V (f : {fmap K -> option V}) k :
  k \in reducef f = ojoin f.[? k].
Proof.
rewrite inE; case: fndP => [kf|] /=; first by rewrite in_FSet in_set.
by apply: contraNF; apply: (fsubsetP (FSet_sub _)).
Qed.

Lemma mem_filterf V (f : {fmap K -> V}) (P : pred K) (k : K) :
  (k \in filterf f P) = (P k) && (k \in f) :> bool.
Proof.
rewrite mem_reducef; case: fndP => [kf|kNf]; last by rewrite andbF.
by rewrite ffunE /=; case: (P k).
Qed.

Lemma mem_remf V (f : {fmap K -> V}) (k k' : K) :
   k \in f.[~ k'] = (k != k') && (k \in f) :> bool.
Proof. by rewrite mem_filterf. Qed.

Lemma mem_remfF V (f : {fmap K -> V}) (k : K) : k \in f.[~ k] = false.
Proof. by rewrite mem_remf eqxx. Qed.

Lemma fnd_reducef  V (f : {fmap K -> option V}) k :
  (reducef f).[? k] = ojoin f.[? k].
Proof.
case: fndP => /= [kf|]; last by rewrite mem_reducef; case: ojoin.
rewrite ffunE /= Some_oextract; apply: Some_inj; rewrite -in_fnd.
by rewrite Some_ojoin // ojoinT // -mem_reducef.
Qed.

End Ops2.

Section FinSFun
.

Variables (K:keyType) (V:eqType) (default : K -> V).

Record finsfun := FinSFun {
  finsfun_of : {fmap K -> V};
  _ : [forall k:domf finsfun_of, finsfun_of k != default (val k)]
}.

Fact finsfun_subproof (f : finsfun) : 
  forall (k : K) (kf : k \in finsfun_of f), (finsfun_of f).[kf] != default k.
Proof. case:f => f f_stable k kf /=. exact (forallP f_stable (SeqSub kf)). Qed.

Definition fun_of_finsfun (f : finsfun) (k : K) :=
  odflt (default k) (finsfun_of f).[? k].     
           
Coercion fun_of_finsfun : finsfun >-> Funclass.

(* à mettre au bon endroit *)
Definition fun_of_ffun (S : {fset K}) (f : {ffun S -> V}) : K -> V :=
  fun k =>
  if (k \in S =P true) is ReflectT k_in_S then f (SeqSub k_in_S) else (default k). 

Lemma in_fun_of_ffun (S : {fset K}) (f : {ffun S -> V}) (k : K) (kf : k \in S) :
  fun_of_ffun f k = f (SeqSub kf).
Proof.
rewrite/fun_of_ffun; case:eqP=> kf'; last by [].
by apply/f_equal/f_equal/bool_irrelevance.
Qed.

Lemma out_fun_of_ffun (S : {fset K}) (f : {ffun S -> V}) (k : K) :
  k \notin S -> fun_of_ffun f k == default k.
Proof. by move => kS; rewrite/fun_of_ffun; case:eqP => kS' //; rewrite kS' in kS. Qed.

Definition finsupp (f : finsfun) := domf (finsfun_of f).

Lemma mem_finsupp (f : finsfun) (k : K) : (k \in finsupp f) = (f k != default k).
Proof.
rewrite /fun_of_finsfun; case: fndP; rewrite ?eqxx //=.
by move=> kf; rewrite finsfun_subproof.
Qed.

Lemma finsfun_dflt (f : finsfun) (k : K) : k \notin finsupp f -> f k = default k.
Proof. by rewrite mem_finsupp negbK => /eqP. Qed.

CoInductive finsfun_spec (f : finsfun) (k : K) : V -> bool -> Type :=
  | FinsfunOut : k \notin finsupp f -> finsfun_spec f k (default k) false
  | FinsfunIn  (kf : k \in finsupp f) : finsfun_spec f k (f k) true.

Lemma finsfunP (f : finsfun) (k : K) : finsfun_spec f k (f k) (k \in finsupp f).
Proof.
have [kf|kNf] := boolP (_ \in _); first by constructor.
by rewrite finsfun_dflt // ; constructor.
Qed.

Variables (f : K -> V) (S : {fset K}).
Definition suppS := FSet [set a : S | f (val a) != default (val a)].
Definition fmapS := FinMap [ffun a : suppS => f (val a)].

Fact finsfunS_subproof : [forall k : suppS, fmapS k != default (val k)].
Proof. apply/forallP => a /=. rewrite ffunE.
by move: (ssvalP a) => /in_FSetE [ka /=]; rewrite in_set.
Qed.

Definition finsfun_of_fun :=
  @FinSFun fmapS finsfunS_subproof.

Lemma finsfun_of_funE : 
  (forall a : K, f a != default a -> a \in S) -> (finsfun_of_fun) =1 f.  
Proof.
move => H a; symmetry.
rewrite/finsfun_of_fun /fun_of_finsfun /=. case: fndP => /=.
by move => kf; rewrite ffunE. 
apply:contraNeq; move=> fa_neq_dflt.
have /H a_in_S := fa_neq_dflt.
by rewrite in_FSet inE /=.
Qed.

(* Définition d'une finsfun à partir d'une ffun qui *)
(* ne fixe aucun point de son domaine. On obtient *)
(* une finsfun dont le support est définitionnellement *)
(* égal au domaine de la finfun *)
 
Definition finsfun_of_can_ffun (T : {fset K}) (g : {ffun T -> V}) 
          (can_g : [forall k : T ,  g k != default (val k)]) :=
  @FinSFun (FinMap g) can_g.

Lemma finsfun_of_can_ffunE (T : {fset K}) (g : {ffun T -> V}) 
          (can_g : [forall k : T ,  g k != default (val k)]) 
          (k : K) (kg : k \in T) :
  (finsfun_of_can_ffun can_g) k = g (SeqSub kg). 
Proof. by rewrite/fun_of_finsfun in_fnd. Qed.

Lemma finsfun_injective_inP  (g : finsfun) :
  reflect {in S &, injective g} (injectiveb [ffun x : S => g (val x)]).
Proof.
apply: (iffP (@injectiveP _ _ _)) => g_inj a b; last first.
  by rewrite !ffunE => *; apply: val_inj; apply: g_inj => //; apply: valP.
move=> aS bS eq_ga_gb; suff: (SeqSub aS) = (SeqSub bS) by move=> [].
by apply: g_inj; rewrite !ffunE.
Qed.

Lemma eq_finsfunP (g h : finsfun) : g =1 h <-> g = h. 
Proof.
split; last by move ->.
case: g; case: h => h can_h g can_g fg_eq_fh. suff g_eq_h : g = h.
  move:g_eq_h can_h can_g fg_eq_fh -> => can_h can_g _. congr FinSFun.
  by apply bool_irrelevance.
apply/fmap_fndP=> k. case:fndP; case:fndP => //.
 - move => kh kg. congr Some. move:(fg_eq_fh k). by rewrite /fun_of_finsfun !in_fnd.
 - move => kNh kf. move : (fg_eq_fh k). rewrite/fun_of_finsfun in_fnd not_fnd //= => /eqP.
   by rewrite (negbTE (forallP can_g (SeqSub kf))).
 - move => kh kNg. move : (fg_eq_fh k). rewrite/fun_of_finsfun not_fnd //= => /eqP.
   by rewrite in_fnd /= eq_sym (negbTE (forallP can_h (SeqSub kh))).
Qed.

End FinSFun.

Section InjectiveFinSFun.

Variables (K : keyType) (V : eqType).


Definition injectiveb_finsfun_id : pred (finsfun (@id K)) :=
  [pred g | (injectiveb [ffun a : finsupp g => g (val a)])
            && [forall a : finsupp g, g (val a) \in finsupp g]].

Lemma injectiveb_finsfunP (g : finsfun (@id K)) :
  reflect (injective g) (injectiveb_finsfun_id g).
Proof. 
rewrite /injectiveb_finsfun_id; apply: (iffP idP).
  move=> /andP [/finsfun_injective_inP inj_g /forallP stable_g ] a b.
  wlog /andP [ag bg] : a b / (a \in finsupp g) && (b \notin finsupp g) => [hwlog|].
    case: (finsfunP g b); case: (finsfunP g a) => //; last by move=> *; exact: inj_g.
      by move=> ag bg ga_eq_b; apply: hwlog; rewrite ?ag ?bg ?(finsfun_dflt bg).
    by move=> ag bg ga_eq_b; symmetry; apply: hwlog; rewrite ?ag ?bg ?(finsfun_dflt ag).
  rewrite (finsfun_dflt bg) => ga_eq_b; move: bg; rewrite -ga_eq_b.
  by rewrite (stable_g (SeqSub ag)).

move => g_inj; apply/andP; split.
  by apply/injectiveP => a b; rewrite !ffunE => eq_ga_gb; apply/val_inj/g_inj.
apply/forallP => a.
by rewrite mem_finsupp (inj_eq g_inj) -mem_finsupp; apply/valP.
Qed.

Lemma injective_finsfunP (g : finsfun (@id K)) :
  injective g <->
  exists2 S : {fset K}, (finsupp g \fsubset S)
  & {in S &, injective g} /\ forall a : S, g (val a) \in S.
Proof.
split => [|[S [finsupp_subset_S [g_inj_in g_stable]]]].
move => /injectiveb_finsfunP /andP [/finsfun_injective_inP g_inj_in /forallP].
  by exists (finsupp g) => //; rewrite fsubsetAA.
move=> a b.
have [[aS|aNS] [bS|bNS]] := (boolP (a \in S), boolP (b \in S)); first 3 last.
- by rewrite !finsfun_dflt // ?(contra (fsubsetP finsupp_subset_S _)).
- exact: g_inj_in.
- rewrite (finsfun_dflt (contra (fsubsetP finsupp_subset_S _) bNS)).
  by move=> ga_eq_b; move: bNS; rewrite -ga_eq_b (g_stable (SeqSub aS)).
rewrite (finsfun_dflt (contra (fsubsetP finsupp_subset_S _) aNS)).
by move=> gb_eq_a; move: aNS; rewrite gb_eq_a (g_stable (SeqSub bS)).
Qed.
  
End InjectiveFinSFun.


(*

Lemma fnd_filterd V (f : {fmap K -> V}) P k :
  (filterf f P).[? k] = if P k then f.[?k] else None.
Proof.
rewrite fnd_reducef.

(* PROOF IN PROGRESS *)


Lemma get_rem V (v0 : V) (f : {fmap K -> V}) (k k' : K) :
  (f.[~ k]).[k' | v0] = if k' == k then v0 else f.[k' | v0].
 Proof.
rewrite (remfE v0) fmapK mem_rem_uniq // inE /=; case: eqP => //= _.
by have [//|kf] := boolP (_ \in _); rewrite get_default.
Qed.

Lemma fnd_rem V (f : {fmap K -> V}) (k k' : K) :
  f.[~ k].[k'] = if k' == k then None else f.[k'].
Proof.
have [_|v _ _] := pre_finmapP f; first by rewrite !fnd_default // if_same.
by rewrite !(fndE v) get_rem mem_remf; case: eqP; case: (_ \in _).
Qed.

Lemma setf_get V (v0 : V) (f : {fmap K -> V}) (k : K) :
 f.[k <- f.[k | v0]] = if k \in f then f else f.[k <- v0].
Proof.
case: ifP => kf; last by rewrite get_default // kf.
apply: (@getP _ v0); first by rewrite keys_set /= kf undup_keys sort_keys.
by move=> k' _; have [->|nk''] := eqVneq k' k;  rewrite (setfK,setfNK).
Qed.

Lemma setf_rem V (f : {fmap K -> V}) (k : K) (v : V) : k \in f ->
  f.[~ k].[k <- v] = f.[k <- v].
Proof.
move=> kf; apply: congr_fmap => k' /=; last by rewrite get_rem; case: eqP.
by rewrite keys_rem !in_cons mem_rem_uniq // inE /=; case: eqP.
Qed.

Lemma setf_mapf V V' (f : {fmap K -> V}) (g : K -> V -> V') (k : K) (v : V) :
  [fmap g k v | k, v <- f].[k <- g k v] = [fmap g k v | k, v <- f.[k <- v]].
Proof.
by apply: fndP => k'; rewrite !(fnd_set, fnd_mapf); case: eqP => // ->.
Qed.

Lemma finMapP V (f : {fmap K -> V}) (k : K) : k \in f ->
  {gv : {fmap K -> V} * V | k \notin gv.1 & f = gv.1.[k <- gv.2]}.
Proof.
move=> kf; have v0 := key_ex_value kf.
exists (remf k f, get v0 f k) => /=; first by rewrite mem_remfF.
by rewrite setf_rem // setf_get kf.
Qed.

CoInductive mem_finmap_spec V (k : K) (f : {fmap K -> V}) :
  {fmap K -> V} -> option V -> bool -> bool -> Type :=
| MemFinmapNil of k \notin f :
    mem_finmap_spec k f f None (keys f == [::]) false
| MemFinmapNNil (v : V) g of f = g.[k <- v] & k \notin g :
    mem_finmap_spec k f (setf g k v) (Some v) false true.

Lemma mem_finmapP V k (f : {fmap K -> V}) :
  mem_finmap_spec k f f f.[k] (keys f == [::]) (k \in f).
Proof.
have [kf|kf] := boolP (_ \in _); last first.
  by rewrite fnd_default //; constructor.
have [[g v] /= kg {-4}->] := finMapP kf.
by rewrite inE in kf *; rewrite fnd_set eqxx; case: keys kf => //; constructor.
Qed.

CoInductive get_finmap_spec V (v0 : V) (k : K) (f : {fmap K -> V}) :
  {fmap K -> V} -> bool -> bool -> option V -> V -> Type :=
| GetFinmapNil of k \notin f :
    get_finmap_spec v0 k f f (keys f == [::]) false None v0
| GetFinmapNNil (v : V) g of f = g.[k <- v] :
    get_finmap_spec v0 k f (g.[k <- v]) false true (Some v) v.

Lemma get_finmapP V v0 k (f : {fmap K -> V}) :
  get_finmap_spec v0 k f f (keys f == [::]) (k \in f)
                           (f.[k]) (f.[k | v0]).
Proof.
have [kf|v g _] := mem_finmapP; first by rewrite get_default //; constructor.
by rewrite setfK; constructor.
Qed.

Lemma setfC V (f : {fmap K -> V}) k1 k2 v1 v2 :
   f.[k1 <- v1].[k2 <- v2] =
   if k2 == k1 then f.[k2 <- v2] else f.[k2 <- v2].[k1 <- v1].
Proof.
apply: fndP => k /=; have [->|Nk12] := altP eqP.
  by rewrite !fnd_set; case: eqP.
by rewrite !fnd_set; have [->|//] := altP eqP; rewrite (negPf Nk12).
Qed.

Lemma remf_id V (f : {fmap K -> V}) k : k \notin f -> f.[~ k] = f.
Proof.
move=> kf; apply: fndP => k'; rewrite fnd_rem.
by case: eqP => // ->; rewrite not_fnd.
Qed.

Lemma remf_set V (f : {fmap K -> V}) (k k' : K) (v : V) :
  f.[k' <- v].[~ k] = if k == k' then f.[~ k] else f.[~ k].[k' <- v].
Proof.
apply: fndP => k'' /=; have [->|Nk12] := altP eqP.
  by rewrite !fnd_rem fnd_set; case: eqP.
by rewrite !(fnd_rem, fnd_set); have [->|//] := altP eqP; rewrite (negPf Nk12).
Qed.

Lemma is_fnd V (f : {fmap K -> V}) k : k \in f -> exists v, f.[k] = Some v.
Proof. by rewrite -fndSome; case: fnd => v //; exists v. Qed.

Lemma setf_inj V (f f' : {fmap K -> V}) k v :
  k \notin f -> k \notin f' -> f.[k <- v] = f'.[k <- v]-> f = f'.
Proof.
move=> kf kf' eq_fkv; apply: fndP => k'; have := congr1 (fnd^~ k') eq_fkv.
by rewrite !fnd_set; case: eqP => // ->; rewrite !fnd_default.
Qed.

CoInductive finmap_spec V (f : {fmap K -> V}) :
  {fmap K -> V} -> seq K -> bool -> Type :=
| FinmapNil of f = nilf : finmap_spec f nilf [::] true
| FinmapNNil (v : V) (k : K) g of f = g.[k <- v] & k \notin g :
    finmap_spec f g.[k <- v] (k :: keys g) false.

Lemma finmapP V (f : {fmap K -> V}) : finmap_spec f f (keys f) (keys f == [::]).
Proof.
have [/finmap_nil->|kf] := altP (keys f =P [::]); first by constructor.
case ekf: keys kf => [//|k ks] _.
case: (mem_finmapP k f); first by rewrite inE ekf mem_head.
move=> v g eq_f kNg; rewrite -{1}eq_f.
suff -> : ks = keys g by constructor.
have -> : g = f.[~ k] by rewrite eq_f remf_set eqxx remf_id.
by rewrite keys_rem ekf /= eqxx.
Qed.

End Theory.
Hint Resolve keys_uniq.
Hint Resolve keys_sortedW.

Section Cat.
Variables (K : keyType).

Definition catf V (f g : {fmap K -> V}) :=
  if (keys g != [::]) =P true is ReflectT P
  then let v := ex_value P in
    fmap (keys f ++ keys g)
         (fun k => if k \in g then g.[k | v] else f.[k | v])
  else f.

Definition disjf V (f g : {fmap K -> V}) : bool :=
  all (predC (mem (keys g))) (keys f).

Lemma disjfP {V} {f g : {fmap K -> V}} :
  reflect {in f & g, forall k k', k != k'} (disjf f g).
Proof.
apply: (iffP idP) => [dfg k k' kf k'g|Hfg].
  by have /allP /(_ _ kf) := dfg; apply: contraNneq => ->.
by apply/allP=> k kf; have /contraTN := Hfg _ k kf; apply.
Qed.

Lemma disjfC  V (f g : {fmap K -> V}) : disjf f g = disjf g f.
Proof. by apply/disjfP/disjfP => Hfg ????; rewrite eq_sym; apply: Hfg. Qed.

Lemma disjfPr {V} {f g : {fmap K -> V}} :
  reflect {in f, forall k, k \in g = false} (disjf f g).
Proof.
apply: (iffP disjfP) => [dfg k kf|dfg k k' kf kg].
  by apply: contraTF isT => /(dfg _ _ kf); rewrite eqxx.
by apply: contraTneq kg => <-; rewrite dfg.
Qed.

Lemma disjfPl {V} {f g : {fmap K -> V}} :
  reflect {in g, forall k, k \in f = false} (disjf f g).
Proof. by rewrite disjfC; apply: disjfPr. Qed.

Lemma disjf0 V (f : {fmap K -> V}) : disjf f nilf.
Proof. by apply/disjfP => k k'. Qed.

Lemma disj0f V (f : {fmap K -> V}) : disjf nilf f.
Proof. by apply/disjfP => k k'. Qed.

Lemma catf0 V (f : {fmap K -> V}) : catf f nilf = f.
Proof. by rewrite /catf; case: eqP. Qed.

Lemma catfE V v0 (f g : {fmap K -> V}) : catf f g =
  fmap (keys f ++ keys g)
       (fun k => if k \in g then g.[k | v0] else f.[k | v0]).
Proof.
rewrite /catf; case: eqP => /= [P|]; last first.
  by have [|//] := finmapP; rewrite cats0 /= getK.
apply/eq_in_fmap => /= k; rewrite mem_cat orbC => kfg.
by case: (boolP (_ \in g)) kfg => //= ? ?; apply: eq_get.
Qed.

Lemma get_cat V v0 (f g : {fmap K -> V}) k :
  get v0 (catf f g) k = if k \in g then g.[k | v0] else f.[k | v0].
Proof.
rewrite (catfE v0) !fmapK mem_cat orbC.
by case: mem_finmapP => //; case: get_finmapP.
Qed.

Lemma keys_cat V (f g : {fmap K -> V}) :
  keys (catf f g) = sort <=%O (undup (keys f ++ keys g)).
Proof.
have [_//=|v _ _] := pre_finmapP g; last by rewrite (catfE v) keys_fmap.
by rewrite catf0 cats0 undup_keys sort_keys.
Qed.

Lemma mem_catf V (f g : {fmap K -> V}) k :
 k \in catf f g = (k \in f) || (k \in g).
Proof. by rewrite inE keys_cat mem_sort mem_undup mem_cat. Qed.

Lemma fnd_cat V (f g : {fmap K -> V}) k :
  fnd (catf f g) k = if k \in g then g.[k] else f.[k].
Proof.
have [_//=|v _ _] := pre_finmapP g; first by rewrite catf0.
by rewrite !(fndE v) /= get_cat mem_catf orbC; do !case: (_ \in _).
Qed.

Lemma cat0f V (f : {fmap K -> V}) : catf nilf f = f.
Proof.
apply: fndP => k; rewrite fnd_cat.
by case: mem_finmapP => // v {f} f _; rewrite fnd_set eqxx.
Qed.

Lemma catf_setl V f g k (v : V) :
  catf f.[k <- v] g = if k \in g then catf f g else (catf f g).[k <- v].
Proof.
apply: fndP => k'0; rewrite !(fnd_cat,fnd_if,fnd_set).
by have [->|Nkk'] := altP eqP; do !case: (_ \in _).
Qed.

Lemma catf_setr V f g k (v : V) : catf f g.[k <- v] = (catf f g).[k <- v].
Proof.
apply: fndP => k'; rewrite !(fnd_cat, fnd_set) mem_setf.
by case: (_ == _); case: (_ \in _).
Qed.

Lemma catf_reml V k (f g : {fmap K -> V}) :
  catf f.[~ k] g = if k \in g then catf f g else (catf f g).[~ k].
Proof.
apply: fndP => k'; rewrite !(fnd_if, fnd_cat, fnd_rem).
by have [->|?] := altP eqP; do !case: (_ \in _).
Qed.

Lemma disjf_setr V (f g : {fmap K -> V}) k v :
  disjf f g.[k <- v] = (k \notin f) && (disjf f g).
Proof.
apply/idP/idP => [dfg|/andP [kf dfg]].
  rewrite (disjfPl dfg) ?mem_setf ?eqxx //=; apply/disjfPl=> k' k'g.
  by rewrite (disjfPl dfg) // mem_setf k'g orbT.
apply/disjfPl => k'; rewrite mem_setf.
by have [->|_ /disjfPl->] := altP eqP; first by rewrite (negPf kf).
Qed.

End Cat.

Section DisjointUnion.
Variables (K : keyType) (V : Type).
Notation finmap := ({fmap K -> V}).
Notation nil := (@nil K V).

Lemma disjf_remr k (s1 s2 : finmap) :
  k \notin s1 -> disjf s1 s2.[~k] = disjf s1 s2.
Proof.
move=> kNs1; apply/disjfPr/disjfPr => Hs2 x xs1; last first.
  by rewrite mem_remf Hs2 // andbF.
have := Hs2 x xs1; rewrite mem_remf; apply: contraFF => ->; rewrite andbT.
by apply: contraNneq kNs1 => <-.
Qed.

Lemma disjf_reml k (s1 s2 : finmap) :
  k \notin s2 -> disjf s1.[~k] s2 = disjf s1 s2.
Proof. by move=> kNs2; rewrite disjfC disjf_remr // disjfC. Qed.

Lemma disjf_catl (s s1 s2 : finmap) :
  disjf s (catf s1 s2) = disjf s s1 && disjf s s2.
Proof.
apply/disjfPr/idP => [Ncat|/andP[/disjfPr Ns1 /disjfPr Ns2]]; last first.
  by move=> k ks /=; rewrite mem_catf Ns1 ?Ns2.
apply/andP; split; apply/disjfPr=> k ks; have := Ncat k ks;
by rewrite mem_catf; apply: contraFF => ->; rewrite ?orbT.
Qed.

Lemma catfC (s1 s2 : finmap) : disjf s1 s2 -> catf s1 s2 = catf s2 s1.
Proof.
move=> ds1s2; apply/fndP => x; rewrite !fnd_cat.
case: ifPn=> [xs2|xNs2]; first by rewrite (disjfPl ds1s2).
by case: ifPn=> [//|xNs1]; rewrite !fnd_default.
Qed.

Lemma catfA (s1 s2 s3 : finmap) :
        disjf s2 s3 -> catf s1 (catf s2 s3) = catf (catf s1 s2) s3.
Proof.
move=> ds2s3; apply: fndP => x; rewrite !fnd_cat !mem_catf.
have [xs3|/= xNs3] := boolP (_ \in s3); last by rewrite orbF.
by rewrite (disjfPl ds2s3).
Qed.

Lemma catfAC (s1 s2 s3 : finmap) :
  [&& disjf s1 s2, disjf s2 s3 & disjf s1 s3] ->
    catf (catf s1 s2) s3 = catf (catf s1 s3) s2.
Proof. by case/and3P=>???; rewrite -!catfA ?(@catfC s2) // disjfC. Qed.

Lemma catfCA (s1 s2 s3 : finmap) :
  [&& disjf s1 s2, disjf s2 s3 & disjf s1 s3] ->
    catf s1 (catf s2 s3) = catf s2 (catf s1 s3).
Proof. by case/and3P=>???; rewrite !catfA ?(@catfC s2) // disjfC. Qed.

Lemma catfsK (s s1 s2 : finmap) :
  disjf s1 s && disjf s2 s -> catf s1 s = catf s2 s -> s1 = s2.
Proof.
move=> /andP[ds1s ds2s] eq_s12s; apply: fndP => k.
move: eq_s12s => /(congr1 (fnd^~ k)); rewrite !fnd_cat.
by case: ifP => // ks _; rewrite !fnd_default ?(disjfPl ds1s) ?(disjfPl ds2s).
Qed.

Lemma catfKs (s s1 s2 : finmap) :
  disjf s s1 && disjf s s2 -> catf s s1 = catf s s2 -> s1 = s2.
Proof.
move=> /andP [??]; rewrite !(@catfC s) //.
by move => /catfsK -> //; apply/andP; split; rewrite disjfC.
Qed.

End DisjointUnion.

Section EqType.
Variables (K : keyType) (V : eqType).

Definition feq (s1 s2 : {fmap K -> V}) := seq_of s1 == seq_of s2.

Lemma feqP : Equality.axiom feq.
Proof.
move=> s1 s2; rewrite /feq; apply: (iffP eqP) => [|->//].
move: s1 s2 => [s1 Hs1] [s2 Hs2] //= eq_s12.
by case: _ / eq_s12 in Hs2 *; rewrite [Hs1]bool_irrelevance.
Qed.

Canonical Structure finmap_eqMixin := EqMixin feqP.
Canonical Structure finmap_eqType := EqType {fmap K -> V} finmap_eqMixin.
End EqType.


Definition fmap_encode V (f : {fmap K -> V}) :
  {ks : seq K & {ffun seq_sub ks -> V}} :=
  Tagged (fun ks => {ffun seq_sub ks -> V}) (ffun_of_fmap f).

Definition fmap_decode V (f : {ks : seq K & {ffun seq_sub ks -> V}}) :
  {fmap K -> V} := [fmap k kf in tag f => tagged f (SeqSub kf)]. 
  
Lemma fmap_encodeK V : cancel (@fmap_encode V) (@fmap_decode V).
Proof.
rewrite /fmap_decode => f; apply/fndP => k //=.
Admitted.

Definition finMapEqMixin (V : eqType) := CanEqMixin (@fmap_encodeK V).
Canonical  finMapEqType  (V : eqType) :=
  EqType ({fmap K -> V}) (@finMapEqMixin V).
Delimit Scope fmap_scope with fset.
Open Scope fmap_scope.

Notation "[ 'fmap' ]" := nilf : fmap_scope.
Infix "++" := catf : fmap_scope.
Infix ":~:" := disjf : fmap_scope.

Section FSet.
Variables (K : keyType).
Implicit Type s : seq K.

Definition fset s : {fset K} := fmap s (fun=> tt).
Notation "u .[+ k ]" := (u.[k <- tt]) : fmap_scope.
Notation "[ 'fset' k ]" := (fset [::k]) : fmap_scope.

Lemma mem_fset (u : {fset K}) i : (i \in u) = (fnd u i == Some tt).
Proof.
by have [/is_fnd [] [->] //|iNu] := boolP (_ \in _); rewrite fnd_default.
Qed.

Lemma mem_fsetP (u : {fset K}) i : reflect (fnd u i = Some tt) (i \in u).
Proof. by rewrite mem_fset; apply: eqP. Qed.

Lemma fsetP (u v : {fset K}) : u =i v <-> u = v.
Proof.
split => [eq_uv|->//]; apply/fndP => i.
have := eq_uv i; have [iv iu|iNv iNu] := boolP (i \in v).
  by rewrite !(mem_fsetP _ _ _).
by rewrite !fnd_default ?iNv ?iNu.
Qed.

Lemma fset_rem s k : uniq s -> fset (rem k s) = remf k (fset s).
Proof.
by move=> s_uniq; apply/fsetP => i; rewrite ?(mem_fmap, mem_remf) mem_rem_uniq.
Qed.

Lemma catf1 u k : u ++ [fset k] = u.[+ k].
Proof.
apply/fsetP=> i.
by rewrite mem_catf mem_fmap in_cons in_nil orbF mem_setf orbC.
Qed.

Lemma add0f k : [fmap].[+ k] = [fset k]. Proof. by apply/fsetP=> i. Qed.

Lemma fset_cat s s' : fset (s ++ s') = fset s ++ fset s'.
Proof. by apply/fsetP=> i; rewrite !(mem_fmap, mem_catf) mem_cat. Qed.

Lemma fset_cons s k : fset (k :: s) = (fset s).[+ k].
Proof. by apply/fsetP => i; rewrite !(mem_fmap, mem_setf) in_cons. Qed.

Lemma fset_rcons s k : fset (rcons s k) = (fset s).[+ k].
Proof.
by apply/fsetP => i; rewrite !(mem_fmap, mem_setf) mem_rcons in_cons.
Qed.

Lemma fset_sort s r : fset (sort r s) = fset s.
Proof. by apply/fsetP => i; rewrite !(mem_fmap, mem_sort). Qed.

Lemma fset_undup s : fset (undup s) = fset s.
Proof. by apply/fsetP => i; rewrite !(mem_fmap, mem_undup). Qed.

Variable (V : Type).
Implicit Types (f g : {fmap K -> V}) (k : K) (v : V).

Definition domf f := fset (keys f).

Lemma mem_domf f k : (k \in domf f) = (k \in f).
Proof. by rewrite mem_fmap. Qed.

Lemma domf_rem f k : domf f.[~k] = (domf f).[~ k].
Proof. by rewrite /domf keys_rem fset_rem. Qed.

Lemma domf_set f k v : domf f.[k <- v] = (domf f).[+ k].
Proof. by rewrite /domf keys_set fset_sort fset_undup fset_cons. Qed.

Lemma domf_cat f g : domf (f ++ g) = domf f ++ domf g.
Proof. by rewrite /domf keys_cat fset_sort fset_undup fset_cat. Qed.

Lemma domf_disj f g : domf f :~: domf g = f :~: g.
Proof.
apply/disjfPr/disjfPl => Hfg k; apply: contraTF.
  by rewrite -mem_domf => /Hfg; rewrite mem_domf => ->.
by rewrite mem_domf => /Hfg; rewrite mem_domf => ->.
Qed.

End FSet.

Section KeysInd.
Variable (K : keyType) (V : Type).

Lemma keys_eq0P {f : {fmap K -> V}} : reflect (f = [fmap]) (keys f == [::]).
Proof. by apply: (iffP idP) => [|-> //]; case: finmapP. Qed.

Lemma fmap_ind (P : {fmap K -> V} -> Type) :
  P [fmap] ->
 (forall (f : {fmap K -> V}) k v,
    k \notin f -> P f -> P f.[k <- v]) ->
 forall f, P f.
Proof.
move=> Pnil Pset f; have := erefl (keys f).
elim: (keys f) {-2}f => [|k ks iks] {f} f.
  by move/eqP; case: (finmapP f).
case: finmapP => // v k' g eq_f kNg [eqk'k kg].
rewrite eqk'k in kNg eq_f * => {k' eqk'k}.
by apply: Pset => //; apply: iks.
Qed.

End KeysInd.

*)

