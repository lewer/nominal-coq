(*************************************************************************)
(* Copyright (C) 2012                                                    *)
(* Author C. Cohen                                                       *)
(* All rights reserved                                                   *)
(* Draft - DO NOT DISTRIBUTE                                             *)
(* License to be determined                                              *)
(*************************************************************************)

Require Import ssreflect ssrbool ssrnat eqtype choice ssrfun seq path.
Require Import fintype finfun bigop finset.

(*****************************************************************************)
(* This file provides a representation of finitely supported maps where      *)
(* the keys K lie in an ordType and the values V in an arbitrary type.       *)
(*                                                                           *)
(*         {fset K} == finite sets of elements of K                          *)
(*    {fmap K -> V} == finitely supported maps from K to V.                  *)
(*                                                                           *)
(* In the remainder, A and B are of type {fset K}.                           *)
(* because of the coercion for {fset K} to Type, writing a : A makes sense   *)
(*                                                                           *)
(*            fset0 == the empty finite set                                  *)
(*         [fset k] == the singleton finite set {k}                          *)
(*          A :&: B == the intersection of A and B                           *)
(*          A :|: B == the union of A and B                                  *)
(*           a |: B == the union of singleton a and B                        *)
(*          A :\: B == the complement of B in A                              *)
(*           A :\ b == A without b                                           *)
(* [disjoint A & B] := A :&: B == 0                                          *)
(*     A \fsubset B == A is a subset of B                                    *)
(*     A \fproper B == A is a proper subset of B                             *)
(*           FSet X == turns X : {set A} into an {fset K}                    *)
(*    fincl AsubB a == turns a : A  into an element of B                     *)
(*                     using a proof AsubB of A \fsubset B                   *)
(*         fsub B A == turns A : {fset K} into a {set B}                     *)
(*           f @: A == the image set of the collective predicate A by f.     *)
(*      f @2:(A, B) == the image set of A x B by the binary function f.      *)
(*                                                                           *)
(*    [fset x : X | P] == the set of all x in X such that P is true          *)
(*                        where P is a predicate on X                        *)
(*  [fset x : X | P & Q] := [set x : X | P && Q].                            *)
(* [fset x : K in A | P] == the set containing the x in A such that P is true*)
(*                      this type P is a predicate on K                      *)
(* [fset x : K in A | P & Q ] :=  [set x : K in A | P && Q].                 *)
(* [fset x in A | P]     :=   [set x : _ in A | P].                          *)
(* [fset x in A | P & Q ] :=  [set x : _ in A | P & Q].                      *)
(*                                                                           *)
(*                                                                           *)
(* [fset E | x in A] == the set of all the values of the expression E, for x *)
(*                     drawn from the collective predicate A.                *)
(* [fset E | x in A & P] == the set of values of E for x drawn from A, such  *)
(*                     that P is true.                                       *)
(* [fset E | x in A, y in B] == the set of values of E for x drawn from A and*)
(*                     and y drawn from B; B may depend on x.                *)
(* [fset E | x : T] == the set of all values of E, with x in type T.         *)
(* [fset E | x : T & P] == the set of values of E for x : T s.t. P is true.  *)
(* [fset E | x : T, y : U in B], [fset E | x : T, y : U in B & P],           *)
(* [fset E | x : T, y : U], [fset E | x : T, y : U & P]                      *)
(*            == type-ranging versions of the binary comprehensions.         *)
(*  [fset E | x : T in A], [fset E | x in A, y], [fset E | x, y & P], etc.   *)
(*            == typed and untyped variants of the comprehensions above.     *)
(*               The types may be required as type inference processes E     *)
(*               before considering A or B. Note that type casts in the      *)
(*               binary comprehension must either be both present or absent  *)
(*               and that there are no untyped variants for single-type      *)
(*               comprehension as Coq parsing confuses [x | P] and [E | x].  *)
(*                                                                           *)
(* Operations on finmaps                                                     *)
(*                                                                           *)
(*           domf f == finite set (of type {fset K}) of keys of f            *)
(*          k \in f == k is a key of f                                       *)
(*           [fmap] == the empty finite map                                  *)
(*       f.[k <- v] == f extended with the mapping k -> v                    *)
(*          f.[: A] == f restricted to A (intersected with domf f)           *)
(*          f.[\ A] == f.[: domf :\: A]                                      *)
(*                  := f where all the keys in A have been removed           *)
(*          f.[~ k] := f.[\ [fset k]                                         *)
(*            f.[p] == returns v if p is a proof of k \in f, and k maps to v *)
(*          f.[? k] == returns Some v if k maps to v, otherwise None         *)
(*            f + g == concatenation of f and g,                             *)
(*                     the keys of g override the keys of f                  *)
(*                                                                           *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "{fmap T }" (at level 0, format "{fmap  T }").
Reserved Notation "{fset K }" (at level 0, format "{fset  K }").
Reserved Notation "x .[ k <- v ]"
  (at level 2, k at level 200, v at level 200, format "x .[ k  <-  v ]").
Reserved Notation "x .[~ k ]" (at level 2, k at level 200, format "x .[~  k ]").
Reserved Notation "x .[: k ]" (at level 2, k at level 200, format "x .[:  k ]").
Reserved Notation "x .[\ k ]" (at level 2, k at level 200, format "x .[\  k ]").
Reserved Notation "x .[? k ]" (at level 2, k at level 200, format "x .[?  k ]").
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

Lemma Some_oextract T (x : option T) (x_ex : x) : Some (oextract x_ex) = x.
Proof. by case: x x_ex. Qed.

Definition ojoin T (x : option (option T)) :=
  if x is Some y then y else None.

Lemma Some_ojoin T (x : option (option T)) : x -> Some (ojoin x) = x.
Proof. by case : x. Qed.

Lemma ojoinT T (x : option (option T)) : ojoin x -> x.
Proof. by case: x. Qed.

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

Definition fset_of A (P : pred A) :=
  fset [seq val x | x <- enum [finType of A] & P x].

Local Notation "[ 'fset' x : A | P ]" := (fset_of (fun x : A => P%B))
  (at level 0, x at level 99, format "[ 'fset'  x  :  A  |  P ]").
Local Notation "[ 'fset'  x  :  T  'in'  A  |  P ]" :=
  (fset_of (fun a : A => (fun x : T => P%B) (val a)))
  (at level 0, x at level 99, only parsing).
Local Notation "[ 'fset' x 'in' A | P ]" := [fset x : _ in A | P]
  (at level 0, x at level 99, format "[ 'fset'  x  'in'  A  |  P ]").

Definition fsetI A B := [fset x : K in A | x \in B].

Definition fsetD A B := [fset x in A | x \notin B].

Definition fsubset A B := fsetI A B == A.

Definition fproper A B := fsubset A B && ~~ fsubset B A.

Definition fdisjoint A B := (fsetI A B == fset0).

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

Notation "[ 'disjoint' A & B ]" := (fdisjoint A B) : fset_scope.

Notation "[ 'fset' x : T | P ]" := (fset_of (fun x : T => P%B))
  (at level 0, x at level 99, format "[ 'fset'  x  :  T  |  P ]") : fset_scope.
Notation "[ 'fset' x : T | P & Q ]" := [fset x : T | P && Q]
  (at level 0, x at level 99, format "[ 'fset'  x  :  T  |  P  &  Q ]") : fset_scope.
Notation "[ 'fset'  x  :  T  'in'  A  |  P ]" :=
  (fset_of (fun a : A => (fun x : T => P%B) (val a)))
  (at level 0, x at level 99, only parsing) : fset_scope.
Notation "[ 'fset' x 'in' A | P ]" := [fset x : _ in A | P]
  (at level 0, x at level 99, format "[ 'fset'  x  'in'  A  |  P ]") : fset_scope.
Notation "[ 'fset'  x  :  T  'in' A  |  P  &  Q ]" := [fset x : T in A | P && Q]
  (at level 0, x at level 99, only parsing) : fset_scope.
Notation "[ 'fset' x 'in' A | P & Q ]" := [fset x in A | P && Q]
  (at level 0, x at level 99,
   format "[ 'fset'  x  'in'  A  |  P  &  Q ]") : fset_scope.

Section Theory.

Variables (K : keyType).
Implicit Types (a b x : K) (A B C D : {fset K}) (pA pB pC : pred K) (s : seq K).

Lemma in_fset s : fset s =i s.
Proof. by move=> a; rewrite sort_keysE. Qed.

Lemma in_in_fset x s : x \in fset s -> x \in s.
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

Lemma in_fset_ofP A (P : pred A) a :
  reflect { aA : a \in A & P (SeqSub aA)} (a \in [fset x : A | P x]).
Proof.
apply: (iffP idP) => [|[aA Pa]]; last first.
  rewrite inE sort_keysE; apply/mapP; exists (SeqSub aA) => //.
  by rewrite mem_filter Pa mem_enum.
rewrite inE sort_keysE => /mapP /= [x]; rewrite mem_filter=> /andP [Px _] ->.
by exists (valP x); set y := SeqSub _; have -> : y = x by apply: val_inj.
Qed.

Lemma in_fset_of A (P : pred A) a (aA : a \in A) :
  a \in [fset x : A | P x] =  P (SeqSub aA).
Proof.
apply/in_fset_ofP/idP=> [[aA']|Pa]; last by exists aA.
by set x := SeqSub _;set y := SeqSub _; have -> : y = x by exact: val_inj.
Qed.

Lemma in_fset_in A pA a : (a \in [fset x in A | pA x]) = (a \in A) && (pA a).
Proof.
by apply/in_fset_ofP/idP => [[/= -> -> //]|/andP [aA pAa]]; exists aA.
Qed.

Lemma val_in_fset A (P : pred A) (k : A) :
  (val k \in [fset k : A | P k]) = P k.
Proof. by have Pk := valP k; rewrite in_fset_of; congr P; apply: val_inj. Qed.

Lemma in_fsetI A B a : (a \in A :&: B) = (a \in A) && (a \in B).
Proof. by rewrite in_fset_in. Qed.

Lemma in_fsetD A B a : (a \in A :\: B) = (a \notin B) && (a \in A).
Proof. by rewrite in_fset_in andbC. Qed.

Lemma in_fsetD1 A b a : (a \in A :\ b) = (a != b) && (a \in A).
Proof. by rewrite in_fsetD in_fset1. Qed.

Definition in_fsetE :=
  (in_fset_in, in_fset0, in_fset1, in_fsetU, in_fset1U, in_fsetI, in_fsetD, in_fsetD1).

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

Lemma fset_of_sub A (P : pred A) : [fset x : A | P x] \fsubset A.
Proof. by apply/fsubsetP => k /in_fset_ofP []. Qed.

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

Lemma fsetULVR x A B : x \in A :|: B -> (x \in A) + (x \in B).
Proof. by rewrite in_fsetU; case: (x \in A); [left|right]. Qed.

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

Lemma fsetUDl (A B C : {fset K}) : A :|: (B :\: C) = (A :|: B) :\: (C :\: A).
Proof. by apply/fsetP=> x; rewrite !in_fsetE; do ?case: (_ \in _). Qed.

Lemma fsetUDr (A B C : {fset K}) : (A :\: B) :|: C = (A :|: C) :\: (B :\: C).
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

Lemma fsetI_eq0 A B : (A :&: B == fset0) = [disjoint A & B].
Proof. by []. Qed.

Lemma fdisjoint_sub {A B} : [disjoint A & B]%fset ->
  forall C : {fset K}, [disjoint fsub C A & fsub C B]%bool.
Proof.
move=> disjointAB C; apply/pred0P => a /=; rewrite !in_fsub.
by have /eqP /fsetP /(_ (val a)) := disjointAB; rewrite !in_fsetE.
Qed.

Lemma disjoint_fsub C A B : A :|: B \fsubset C ->
  [disjoint fsub C A & fsub C B]%bool = [disjoint A & B].
Proof.
move=> ABsubC.
apply/idP/idP=> [/pred0P DAB|/fdisjoint_sub->//]; apply/eqP/fsetP=> a.
rewrite !in_fsetE; have [aC|] := boolP (a \in A :|: B); last first.
  by rewrite !in_fsetE => /norP [/negPf-> /negPf->].
by have /= := DAB (SeqSub (fsubsetP ABsubC _ aC)); rewrite !(@in_fsub C).
Qed.

Lemma fdisjointP {A B} :
  reflect (forall a, a \in A -> a \notin B) [disjoint A & B]%fset.
Proof.
apply: (iffP eqP) => [AIB_eq0 a aA|neq_ab].
  by have /fsetP /(_ a) := AIB_eq0; rewrite !in_fsetE aA /= => ->.
apply/fsetP => a; rewrite !in_fsetE.
by case: (boolP (a \in A)) => // /neq_ab /negPf ->.
Qed.

Lemma fsetDidPl A B : reflect (A :\: B = A) [disjoint A & B]%fset.
Proof.
apply: (iffP fdisjointP)=> [NB|<- a]; last by rewrite in_fsetE => /andP[].
apply/fsetP => a; rewrite !in_fsetE andbC.
by case: (boolP (a \in A)) => //= /NB ->.
Qed.

Lemma disjoint_fsetI0 A B : [disjoint A & B] -> A :&: B = fset0.
Proof. by rewrite -fsetI_eq0; move/eqP. Qed.

Lemma fsubsetD A B C :
  (A \fsubset (B :\: C)) = (A \fsubset B) && [disjoint A & C]%fset.
Proof.
pose D := A :|: B :|: C => [:].
have AD : A \fsubset D by rewrite /D -fsetUA fsubsetUl.
have BD : B \fsubset D by rewrite /D fsetUAC fsubsetUr.
rewrite -(@subset_fsubE D) //; last first.
  by rewrite fsubDset (fsubset_trans BD) // fsubsetUr.
rewrite fsubD subsetD !subset_fsubE // disjoint_fsub //.
by rewrite /D fsetUAC fsubsetUl.
Qed.

Lemma fsubsetDP A B C :
   reflect (A \fsubset B /\ [disjoint A & C]%fset) (A \fsubset (B :\: C)).
Proof. by rewrite fsubsetD; apply: andP. Qed.

Lemma fdisjoint_sym A B : [disjoint A & B] = [disjoint B & A].
Proof. by rewrite -!fsetI_eq0 fsetIC. Qed.

Lemma fdisjointP_sym {A B} :
  reflect (forall a, a \in A -> a \notin B) [disjoint B & A]%fset.
Proof. by rewrite fdisjoint_sym; apply: fdisjointP. Qed.

Lemma fdisjoint_trans A B C :
   A \fsubset B -> [disjoint B & C] -> [disjoint A & C].
Proof.
move=> AsubB; rewrite -!(@disjoint_fsub (B :|: C)) ?fsetSU //.
by apply: disjoint_trans; rewrite subset_fsub.
Qed.

Lemma fdisjoint0X A : [disjoint fset0 & A].
Proof. by rewrite -fsetI_eq0 fset0I. Qed.

Lemma fdisjointX0 A : [disjoint A & fset0].
Proof. by rewrite -fsetI_eq0 fsetI0. Qed.

Lemma fdisjoint1X x A : [disjoint [fset x] & A] = (x \notin A).
Proof.
rewrite -(@disjoint_fsub (x |: A)) //;
rewrite (@eq_disjoint1 _ (SeqSub (fset1U1 _ _))) ?(@in_fsub (x |: A)) //=.
by move=> b; rewrite (@in_fsub (x |: _)) [in RHS]inE in_fsetE.
Qed.

Lemma fdisjointX1 x A : [disjoint A & [fset x]] = (x \notin A).
Proof. by rewrite fdisjoint_sym fdisjoint1X. Qed.

Lemma fdisjointUX A B C :
   [disjoint A :|: B & C] = [disjoint A & C]%fset && [disjoint B & C]%fset.
Proof. by rewrite -!fsetI_eq0 fsetIUl fsetU_eq0. Qed.

Lemma fdisjointXU A B C :
   [disjoint A & B :|: C] = [disjoint A & B]%fset && [disjoint A & C]%fset.
Proof. by rewrite -!fsetI_eq0 fsetIUr fsetU_eq0. Qed.

Lemma fdisjointU1X x A B :
   [disjoint x |: A & B]%fset = (x \notin B) && [disjoint A & B]%fset.
Proof. by rewrite fdisjointUX fdisjoint1X. Qed.

End Theory.

Notation Local imfset_def :=
  (fun (K : keyType) (T : finType) (f : T -> K) (P : mem_pred T) =>
  fset [seq f x | x <- enum P]).
Notation Local imfset2_def :=
  (fun (K : keyType) (T1 T2 : finType) (f : T1 -> T2 -> K)
      (P1 : mem_pred T1) (P2 : T1 -> mem_pred T2) =>
  fset (flatten [seq [seq f x y | y <- enum (P2 x)]| x <- enum P1])).


Module Type ImfsetSig.
Parameter imfset : forall (K : keyType) (T : finType),
                   (T -> K) -> mem_pred T -> {fset K}.
Parameter imfset2 : forall (K : keyType) (T1 T2 : finType),
                   (T1 -> T2 -> K) -> mem_pred T1 -> (T1 -> mem_pred T2) ->
                   {fset K}.
Axiom imfsetE : imfset = imfset_def.
Axiom imfset2E : imfset2 = imfset2_def.
End ImfsetSig.

Module Imfset : ImfsetSig.
Definition imfset := imfset_def.
Definition imfset2 := imfset2_def.
Lemma imfsetE : imfset = imfset_def. Proof. by []. Qed.
Lemma imfset2E : imfset2 = imfset2_def. Proof. by []. Qed.
End Imfset.

Notation imfset := Imfset.imfset.
Notation imfset2 := Imfset.imfset2.
Canonical imfset_unlock := Unlockable Imfset.imfsetE.
Canonical imfset2_unlock := Unlockable Imfset.imfset2E.

Notation "f @: A" := (imfset f (mem A)) (at level 24) : fset_scope.
Notation "f @2: ( A , B )" := (imfset2 f (mem A) (fun _ => mem B))
  (at level 24, format "f  @2:  ( A ,  B )") : fset_scope.

(* Comprehensions *)
Notation "[ 'fset' E | x 'in' A ]" := ((fun x => E) @: A)
  (at level 0, E, x at level 99,
   format "[ '[hv' 'fset'  E '/ '  |  x  'in'  A ] ']'") : fset_scope.
Notation "[ 'fset' E | x 'in' A & P ]" := [fset E | x in [fset x in A | P]]
  (at level 0, E, x at level 99,
   format "[ '[hv' 'fset'  E '/ '  |  x  'in'  A '/ '  &  P ] ']'") : fset_scope.
Notation "[ 'fset' E | x 'in' A , y 'in' B ]" :=
  (imfset2 (fun x y => E) (mem A) (fun x => (mem B)))
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'fset'  E '/ '  |  x  'in'  A , '/   '  y  'in'  B ] ']'"
  ) : fset_scope.
Notation "[ 'fset' E | x 'in' A , y 'in' B & P ]" :=
  [fset E | x in A, y in [fset y in B | P]]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'fset'  E '/ '  |  x  'in'  A , '/   '  y  'in'  B '/ '  &  P ] ']'"
  ) : fset_scope.

(* Typed variants. *)
Notation "[ 'fset' E | x : T 'in' A ]" := ((fun x : T => E) @: A)
  (at level 0, E, x at level 99, only parsing) : fset_scope.
Notation "[ 'fset' E | x : T 'in' A & P ]" :=
  [fset E | x : T in [set x : T in A | P]]
  (at level 0, E, x at level 99, only parsing) : fset_scope.
Notation "[ 'fset' E | x : T 'in' A , y : U 'in' B ]" :=
  (imset2 (fun (x : T) (y : U) => E) (mem A) (fun (x : T) => (mem B)))
  (at level 0, E, x, y at level 99, only parsing) : fset_scope.
Notation "[ 'fset' E | x : T 'in' A , y : U 'in' B & P ]" :=
  [fset E | x : T in A, y : U in [set y : U in B | P]]
  (at level 0, E, x, y at level 99, only parsing) : fset_scope.

(* Comprehensions over a type. *)
Local Notation predOfType T := (sort_of_simpl_pred (@pred_of_argType T)).
Notation "[ 'fset' E | x : T ]" := [fset E | x : T in predOfType T]
  (at level 0, E, x at level 99,
   format "[ '[hv' 'fset'  E '/ '  |  x  :  T ] ']'") : fset_scope.
Notation "[ 'fset' E | x : T & P ]" := [fset E | x : T in [set x : T | P]]
  (at level 0, E, x at level 99,
   format "[ '[hv' 'fset'  E '/ '  |  x  :  T '/ '  &  P ] ']'") : fset_scope.
Notation "[ 'fset' E | x : T , y : U 'in' B ]" :=
  [fset E | x : T in predOfType T, y : U in B]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'fset'  E '/ '  |  x  :  T , '/   '  y  :  U  'in'  B ] ']'")
   : fset_scope.
Notation "[ 'fset' E | x : T , y : U 'in' B & P ]" :=
  [fset E | x : T, y : U in [fset y in B | P]]
  (at level 0, E, x, y at level 99, format
 "[ '[hv ' 'fset'  E '/'  |  x  :  T , '/  '  y  :  U  'in'  B '/'  &  P ] ']'"
  ) : fset_scope.
Notation "[ 'fset' E | x : T 'in' A , y : U ]" :=
  [fset E | x : T in A, y : U in predOfType U]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'fset'  E '/ '  |  x  :  T  'in'  A , '/   '  y  :  U ] ']'")
   : fset_scope.
Notation "[ 'fset' E | x : T 'in' A , y : U & P ]" :=
  [fset E | x : T in A, y : U in [set y in P]]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'fset'  E '/ '  |  x  :  T  'in'  A , '/   '  y  :  U  &  P ] ']'")
   : fset_scope.
Notation "[ 'fset' E | x : T , y : U ]" :=
  [fset E | x : T, y : U in predOfType U]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'fset'  E '/ '  |  x  :  T , '/   '  y  :  U ] ']'")
   : fset_scope.
Notation "[ 'fset' E | x : T , y : U & P ]" :=
  [fset E | x : T, y : U in [set y in P]]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'fset'  E '/ '  |  x  :  T , '/   '  y  :  U  &  P ] ']'")
   : fset_scope.

(* Untyped variants. *)
Notation "[ 'fset' E | x , y 'in' B ]" := [fset E | x : _, y : _ in B]
  (at level 0, E, x, y at level 99, only parsing) : fset_scope.
Notation "[ 'fset' E | x , y 'in' B & P ]" := [fset E | x : _, y : _ in B & P]
  (at level 0, E, x, y at level 99, only parsing) : fset_scope.
Notation "[ 'fset' E | x 'in' A , y ]" := [fset E | x : _ in A, y : _]
  (at level 0, E, x, y at level 99, only parsing) : fset_scope.
Notation "[ 'fset' E | x 'in' A , y & P ]" := [fset E | x : _ in A, y : _ & P]
  (at level 0, E, x, y at level 99, only parsing) : fset_scope.
Notation "[ 'fset' E | x , y ]" := [fset E | x : _, y : _]
  (at level 0, E, x, y at level 99, only parsing) : fset_scope.
Notation "[ 'fset' E | x , y & P ]" := [fset E | x : _, y : _ & P ]
  (at level 0, E, x, y at level 99, only parsing) : fset_scope.

(* Print-only variants to work around the Coq pretty-printer K-term kink. *)
Notation "[ 'fse' 't' E | x 'in' A , y 'in' B ]" :=
  (imset2 (fun x y => E) (mem A) (fun _ => mem B))
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'fse' 't'  E '/ '  |  x  'in'  A , '/   '  y  'in'  B ] ']'")
   : fset_scope.
Notation "[ 'fse' 't' E | x 'in' A , y 'in' B & P ]" :=
  [se t E | x in A, y in [fset y in B | P]]
  (at level 0, E, x, y at level 99, format
 "[ '[hv ' 'fse' 't'  E '/'  |  x  'in'  A , '/  '  y  'in'  B '/'  &  P ] ']'"
  ) : fset_scope.
Notation "[ 'fse' 't' E | x : T , y : U 'in' B ]" :=
  (imset2 (fun x (y : U) => E) (mem (predOfType T)) (fun _ => mem B))
  (at level 0, E, x, y at level 99, format
   "[ '[hv ' 'fse' 't'  E '/'  |  x  :  T , '/  '  y  :  U  'in'  B ] ']'")
   : fset_scope.
Notation "[ 'fse' 't' E | x : T , y : U 'in' B & P ]" :=
  [se t E | x : T, y : U in [fset y in B | P]]
  (at level 0, E, x, y at level 99, format
"[ '[hv ' 'fse' 't'  E '/'  |  x  :  T , '/  '  y  :  U  'in'  B '/'  &  P ] ']'"
  ) : fset_scope.
Notation "[ 'fse' 't' E | x : T 'in' A , y : U ]" :=
  (imset2 (fun x y => E) (mem A) (fun _ : T => mem (predOfType U)))
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'fse' 't'  E '/ '  |  x  :  T  'in'  A , '/   '  y  :  U ] ']'")
   : fset_scope.
Notation "[ 'fse' 't' E | x : T 'in' A , y : U & P ]" :=
  (imset2 (fun x (y : U) => E) (mem A) (fun _ : T => mem [fset y \in P]))
  (at level 0, E, x, y at level 99, format
"[ '[hv ' 'fse' 't'  E '/'  |  x  :  T  'in'  A , '/  '  y  :  U '/'  &  P ] ']'"
  ) : fset_scope.
Notation "[ 'fse' 't' E | x : T , y : U ]" :=
  [se t E | x : T, y : U in predOfType U]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'fse' 't'  E '/ '  |  x  :  T , '/   '  y  :  U ] ']'")
   : fset_scope.
Notation "[ 'fse' 't' E | x : T , y : U & P ]" :=
  [se t E | x : T, y : U in [set y in P]]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'fse' 't'  E '/'  |  x  :  T , '/   '  y  :  U '/'  &  P ] ']'")
   : fset_scope.

Section imfset.

Variable (K : keyType).
Implicit Types (A B : {fset K}).

Definition FSet A (X : {set A}) := [fset val k | k : A in X].

Lemma imfsetP (T : finType) (f : T -> K) (D : mem_pred T) (k : K) :
  reflect (exists2 x : T, in_mem x D & k = f x) (k \in imfset f D).
Proof. by rewrite unlock inE /= sort_keysE; exact: imageP. Qed.

Lemma in_imfset (T : finType) (f : T -> K) (D : pred T) (x : T) :
   x \in D -> f x \in [fset f x | x in D].
Proof. by move=> xD; apply/imfsetP; exists x. Qed.

Lemma mem_imfset (T : finType) (f : T -> K) (D : pred T): injective f ->
  forall (k : T), (f k \in [fset f x | x in D]) = (k \in D).
Proof. by move=> f_inj k; rewrite unlock inE /= sort_keysE mem_image. Qed.

Lemma imfset2P (T1 T2 : finType) (f : T1 -> T2 -> K)
      (D1 : mem_pred T1) (D2 : T1 -> mem_pred T2) (k : K) :
  reflect (exists2 x : T1, in_mem x D1
         & exists2 y : T2, in_mem y (D2 x) & k = f x y)
          (k \in imfset2 f D1 D2).
Proof.
rewrite unlock !inE /= !sort_keysE.
apply: (iffP flatten_mapP) => [[x xD1 /mapP [y yD2]]|[x xD1 [y yD2]]] ->.
  by rewrite !mem_enum in xD1 yD2; exists x => //; exists y.
by exists x; rewrite ?mem_enum //; apply/mapP; exists y; rewrite ?mem_enum.
Qed.

Lemma in_imfset2 (T1 T2 : finType) (f : T1 -> T2 -> K)
      (D1 : mem_pred T1) (D2 : T1 -> mem_pred T2) (k : K) (x : T1) (y : T2) :
   x \in D1 -> y \in D2 x -> f x y \in [fset f x y | x in D1, y in D2 x].
Proof. by move=> xD1 yD2; apply/imfset2P; exists x => //; exists y. Qed.


Lemma val_in_FSet A (X : {set A}) (k : A) : (val k \in FSet X) = (k \in X).
Proof. by rewrite mem_imfset //; apply: val_inj. Qed.

Lemma in_FSet A (X : {set A}) (k : K) (kA : k \in A) :
  (k \in FSet X) = (SeqSub kA \in X).
Proof. by rewrite -val_in_FSet. Qed.

Lemma FSetP A (X : {set A}) (k : K) :
  reflect {kA : k \in A & SeqSub kA \in X} (k \in FSet X).
Proof.
apply: (iffP idP) => [|[kA kA_X]]; last by rewrite in_FSet.
rewrite /FSet unlock inE sort_keysE => /mapP [/= x x_in_X ->].
exists (valP x); rewrite mem_enum in x_in_X.
by set y := (y in y \in X); suff <- : x = y by []; apply: val_inj.
Qed.

Lemma FSetE A (X : {set A}) :  FSet X = [fset k : A | k \in X].
Proof. by apply/fsetP=> k; apply/FSetP/in_fset_ofP. Qed.

Lemma FSet_sub A (X : {set A}) : FSet X \fsubset A.
Proof. by apply/fsubsetP => k /FSetP []. Qed.

Lemma fsubK A B : A \fsubset B -> FSet (fsub B A) = A.
Proof.
move=> AsubB; apply/fsetP => k /=; symmetry.
have [kB|kNB] := (boolP (k \in B)); first by rewrite in_FSet in_fsub.
rewrite (contraNF (fsubsetP (FSet_sub _) _)) //.
by apply: contraNF kNB; apply: fsubsetP.
Qed.

Lemma FSetK A (X : {set A}) : fsub A (FSet X) = X.
Proof. by apply/setP => x; rewrite in_fsub val_in_FSet. Qed.

End imfset.

Section DefMap.
Variables (K : keyType) (V : Type).

Record finMap : Type := FinMap {
  domf : {fset K};
  ffun_of_fmap :> {ffun domf -> V}
}.

Definition finmap_of (_ : phant (K -> V)) := finMap.

Let T_ (domf : {fset K}) :=  {ffun domf -> V}.
Local Notation finMap' := {domf : _ & T_ domf}.

End DefMap.

Notation "{fmap T }" := (@finmap_of _ _ (Phant T)) : type_scope.

Definition pred_of_finmap (K : keyType) (V : Type)
  (f : {fmap K -> V}) : pred K := mem (domf f).
Canonical finMapPredType (K : keyType) (V : Type) :=
  Eval hnf in mkPredType (@pred_of_finmap K V).

Delimit Scope fmap_scope with fmap.
Local Open Scope fmap_scope.
Notation "f .[ kf ]" := (f (SeqSub kf)) : fmap_scope.
Arguments ffun_of_fmap : simpl never.

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

Notation "[fmap]" := nilf : fmap_scope.
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

Lemma eq_getf V (A : {fset K}) (f : {ffun A -> V}) k (kf kf' : k \in A) :
  f.[kf] = f.[kf'] :> V.
Proof. by congr f.[_]; apply: bool_irrelevance. Qed.

Lemma Some_fnd V  (f : {fmap K -> V}) (k : domf f) : Some (f k) = f.[? val k].
Proof. by case: fndP (valP k) => // ? _; rewrite getfE. Qed.

Lemma in_fnd V  (f : {fmap K -> V}) (k : K)
      (kf : k \in f) : f.[? k] = Some f.[kf].
Proof. by have := kf; case: fndP => // kf' _; congr Some; apply: eq_getf. Qed.

Lemma getfP V (f g : {fmap K -> V}) : domf f = domf g ->
  (forall k (kMf : k \in f) (kMg : k \in g), f.[kMf] = g.[kMg]) -> f = g.
Proof.
move: f g => [kf f] [kg g] /= eq_kfg; case: _ / eq_kfg in g * => {kg}.
move=> eq_fg; congr FinMap; apply/ffunP => /= x.
by do [rewrite -!getfE; do ?exact: valP] => *.
Qed.

Lemma fmapP V (f g : {fmap K -> V}) : fnd f =1 fnd g <-> f = g.
Proof.
split=> [fnd_fg|-> //]; apply: getfP => [|k kMf kMg].
  by apply/fsetP => x; rewrite -!fndSome fnd_fg.
by apply: Some_inj; rewrite -!in_fnd.
Qed.

Lemma mem_setf V (f : {fmap K -> V}) (k0 : K) (v0 : V) :
  f.[k0 <- v0] =i predU1 k0 (mem (domf f)).
Proof. by move=> k; rewrite !in_fsetE !inE. Qed.

Lemma dom_setf V (f : {fmap K -> V}) (k0 : K) (v0 : V) :
  domf (f.[k0 <- v0]) = k0 |: domf f.
Proof. by apply/fsetP=> k; rewrite mem_setf. Qed.

Lemma fnd_set_in V (f : {fmap K -> V}) k0 v0 (x : domf f.[k0 <- v0]) :
  val x != k0 -> val x \in f.
Proof. by have := valP x; rewrite mem_setf inE; case: eqP. Qed.

Lemma setfK V (f : {fmap K -> V}) k0 v0 (x : domf f.[k0 <- v0]):
   f.[k0 <- v0] x = if eqVneq (val x) k0 is right xNk0
                    then f.[fnd_set_in xNk0] else v0.
Proof.
case: eqVneq => [|xNk0]; rewrite ?ffunE /=; first by move->; rewrite eqxx.
by rewrite (negPf xNk0) in_fnd ?fnd_set_in //= => xf; apply: eq_getf.
Qed.

Lemma fnd_set V (f : {fmap K -> V}) k0 v0 k :
   f.[k0 <- v0].[? k] = if k == k0 then Some v0 else f.[? k].
Proof.
case: fndP => [ksf|]; last first.
  by rewrite mem_setf inE negb_or => /andP [/negPf ->]; case: fndP.
rewrite setfK; case: eqVneq => //= [->|kNk0]; first by rewrite eqxx.
by rewrite -in_fnd (negPf kNk0).
Qed.

Lemma fmap_nil V (f : {fmap K -> V}) : domf f = fset0 -> f = [fmap].
Proof. by move=> kf0; apply: getfP. Qed.

Lemma getf_set V (f : {fmap K -> V}) (k : K) (v : V) (kf' : k \in _) :
   f.[k <- v].[kf'] = v.
Proof. by apply: Some_inj; rewrite -in_fnd fnd_set eqxx. Qed.

Lemma setf_get V (f : {fmap K -> V}) (k : domf f) :
  f.[val k <- f k] = f.
Proof. by apply/fmapP=> k'; rewrite fnd_set Some_fnd; case: eqP => [->|]. Qed.

Lemma setfNK V (f : {fmap K -> V}) (k k' : K) (v : V)
      (k'f : k' \in _) (k'f' : k' \in _):
   f.[k <- v].[k'f'] = if k' == k then v else f.[k'f].
Proof. by apply: Some_inj; rewrite -in_fnd !fnd_set in_fnd; case: ifP. Qed.

End MapTheory.

Section ReduceOp.

Variable (K : keyType) (V : Type).
Implicit Types (f : {fmap K -> option V}).

Lemma reducef_subproof f
      (X := [fset x : domf f | f x])
      (x : X) (x' := (SeqSub (fsubsetP (fset_of_sub _) _ (valP x)))) : f x'.
Proof.
suff : val x' \in X by rewrite val_in_fset.
by have -> : val x' = val x by []; last apply: valP.
Qed.

Definition reducef f : {fmap K -> V} :=
  FinMap [ffun x => oextract (@reducef_subproof f x)].

Lemma domf_reduce f : domf (reducef f) = [fset k : domf f | f k].
Proof. by []. Qed.

Lemma mem_reducef f k : k \in reducef f = ojoin f.[? k].
Proof.
rewrite inE; case: fndP => [kf|] /=; first by rewrite in_fset_of.
by apply: contraNF; apply: (fsubsetP (fset_of_sub _)).
Qed.

Lemma fnd_reducef f k : (reducef f).[? k] = ojoin f.[? k].
Proof.
case: fndP => /= [kf|]; last by rewrite mem_reducef; case: ojoin.
rewrite ffunE /= Some_oextract; apply: Some_inj; rewrite -in_fnd.
by rewrite Some_ojoin // ojoinT // -mem_reducef.
Qed.

Lemma get_reducef f k (krf : k \in reducef f) (kf : k \in f):
  Some (reducef f).[krf] = f.[kf].
Proof. by rewrite -in_fnd fnd_reducef in_fnd. Qed.

End ReduceOp.

Arguments reducef : simpl never.

Section RestrictionOps.

Variable (K : keyType) (V : Type).
Implicit Types (f g : {fmap K -> V}).

Definition filterf f (P : pred K) := reducef
  (FinMap [ffun x : domf f => if P (val x) then Some (f x) else None]).

Definition restrictf f (A : {fset K}) :=  filterf f (mem A).

Notation "x .[: A ]" := (restrictf x A) : fmap_scope.
Notation "x .[\ A ]" := (x.[: domf x :\: A]) : fmap_scope.
Notation "x .[~ k ]" := (x.[\ [fset k]]) : fmap_scope.

Lemma mem_filterf f (P : pred K) (k : K) :
  (k \in filterf f P) = (k \in f) && (P k) :> bool.
Proof.
rewrite mem_reducef; case: fndP => [kf|kNf //].
by rewrite ffunE /=; case: (P _).
Qed.

Lemma domf_filterf f (P : pred K) :
 domf (filterf f P) = [fset k in domf f | P k].
Proof. by apply/fsetP => k; rewrite mem_filterf in_fsetE. Qed.

Lemma mem_restrictf f (A : {fset K}) (k : K) :
   k \in f.[: A] = (k \in A) && (k \in f) :> bool.
Proof. by rewrite mem_filterf andbC. Qed.

Lemma mem_remf f (A : {fset K}) (k : K) :
   k \in f.[\ A] = (k \notin A) && (k \in f) :> bool.
Proof. by rewrite mem_restrictf in_fsetE -andbA andbb. Qed.

Lemma mem_remf1 f (k' k : K) :
   k \in f.[~ k'] = (k != k') && (k \in f) :> bool.
Proof. by rewrite mem_remf in_fsetE. Qed.

Lemma domf_restrict f A : domf f.[: A] = A :&: domf f.
Proof. by apply/fsetP=> k'; rewrite mem_restrictf !in_fsetE. Qed.

Lemma domf_rem f A : domf f.[\ A] = domf f :\: A.
Proof. by rewrite domf_restrict fsetIDAC fsetIid. Qed.

Lemma mem_remfF f (k : K) : k \in f.[~ k] = false.
Proof. by rewrite mem_remf1 eqxx. Qed.

Lemma fnd_filterf f P k : (filterf f P).[? k] = if P k then f.[? k] else None.
Proof.
rewrite fnd_reducef; have [[] Pk [] kf] := (ifP, fndP f k);
do ?by [rewrite in_fnd ?ffunE /= ?Pk|rewrite not_fnd ?ffunE /= ?Pk].
Qed.

Lemma get_filterf f P k (kff : k \in filterf f P) (kf : k \in f) :
  (filterf f P).[kff] = f.[kf].
Proof.
apply: Some_inj; rewrite get_reducef ffunE /=; case: ifPn => //.
by move: kff; rewrite mem_filterf => /andP [? ->].
Qed.

Lemma fnd_restrict f A (k : K) :
   f.[: A].[? k] = if k \in A then f.[? k] else None.
Proof. by rewrite fnd_filterf. Qed.

Lemma fnd_rem f A (k : K) : f.[\ A].[? k] = if k \in A then None else f.[? k].
Proof.
rewrite fnd_restrict in_fsetE.
by case: fndP => ?; rewrite ?(andbT, andbF) //=; case: (_ \in _).
Qed.

Lemma restrictf_comp f A B : f.[: A].[: B] = f.[: A :&: B].
Proof.
by apply/fmapP=> k; rewrite !fnd_restrict !in_fsetE; do !case: (_ \in _).
Qed.

Lemma remf_comp f A B : f.[\ A].[\ B] = f.[\ A :|: B].
Proof. by apply/fmapP=> k; rewrite !fnd_rem in_fsetE; do !case: (_ \in _). Qed.

Lemma restrictfT f : f.[: domf f] = f.
Proof. by apply/fmapP=> k; rewrite fnd_restrict; case: fndP. Qed.

Lemma restrictf0 f : f.[: fset0] = [fmap].
Proof. by apply/fmapP => k; rewrite fnd_restrict in_fsetE not_fnd. Qed.

Lemma remf0 f : f.[\ fset0] = f. Proof. by rewrite fsetD0 restrictfT. Qed.

Lemma fnd_rem1 f (k k' : K) :
  f.[~ k].[? k'] = if k' != k then f.[? k'] else None.
Proof. by rewrite fnd_rem in_fsetE; case: eqP. Qed.

Lemma getf_restrict f A (k : K) (kf : k \in f) (kfA : k \in f.[: A]) :
      f.[: A].[kfA] = f.[kf].
Proof. by rewrite get_filterf. Qed.

Lemma setf_restrict f A (k : K) (v : V) :
  f.[: A].[k <- v] = f.[k <- v].[: k |: A].
Proof.
by apply/fmapP=> k'; rewrite !(fnd_set, fnd_restrict, in_fsetE); case: eqP.
Qed.

Lemma setf_rem f A (k : K) (v : V) :
  f.[\ A].[k <- v] = f.[k <- v].[\ (A :\ k)].
Proof. by rewrite setf_restrict fsetUDl. Qed.

Lemma setf_rem1 f (k : K) (v : V) : f.[~ k].[k <- v] = f.[k <- v].
Proof. by rewrite setf_rem fsetDv remf0. Qed.

Lemma setfC f k1 k2 v1 v2 : f.[k1 <- v1].[k2 <- v2] =
   if k2 == k1 then f.[k2 <- v2] else f.[k2 <- v2].[k1 <- v1].
Proof.
apply/fmapP => k; rewrite (fun_if (fnd^~ k)) !fnd_set.
have [[->|kNk2] [// <-|k2Nk1]] // := (altP (k =P k2), altP (k2 =P k1)).
by rewrite (negPf kNk2).
Qed.

Lemma restrictf_mkdom f A : f.[: A] = f.[: domf f :&: A].
Proof.
apply/fmapP=> k; rewrite !fnd_restrict in_fsetE.
by case: fndP => ?; rewrite ?(andbT, andbF) //=; case: (_ \in _).
Qed.

Lemma restrictf_id f A : [disjoint domf f & A] -> f.[: A] = [fmap].
Proof. by move=> dAf; rewrite restrictf_mkdom (eqP dAf) restrictf0. Qed.

Lemma remf_id f A : [disjoint domf f & A] -> f.[\ A] = f.
Proof. by move=> /fsetDidPl ->; rewrite restrictfT. Qed.

Lemma remf1_id f k : k \notin f -> f.[~ k] = f.
Proof. by move=> kNf; rewrite remf_id //= fdisjointX1. Qed.

Lemma restrictf_set f A (k : K) (v : V) :
  f.[k <- v].[: A] = if k \in A then f.[: A].[k <- v] else f.[: A].
Proof.
apply/fmapP => k' /=; rewrite (fun_if (fnd^~ _)) !(fnd_restrict, fnd_set).
by case: eqP => [->|]; do !case: ifP.
Qed.

Lemma remf_set f A (k : K) (v : V) :
  f.[k <- v].[\ A] = if k \in A then f.[\ A] else f.[\ A].[k <- v].
Proof.
apply/fmapP => k' /=; rewrite (fun_if (fnd^~ _)) !(fnd_rem, fnd_set).
by case: eqP => [->|]; do !case: ifP.
Qed.

Lemma remf1_set f (k k' : K) (v : V) :
  f.[k' <- v].[~ k] = if k == k' then f.[~ k] else f.[~ k].[k' <- v].
Proof. by rewrite remf_set in_fsetE eq_sym. Qed.

Lemma setf_inj f f' k v : k \notin f -> k \notin f' ->
                          f.[k <- v] = f'.[k <- v]-> f = f'.
Proof.
move=> kf kf' eq_fkv; apply/fmapP => k'; have := congr1 (fnd^~ k') eq_fkv.
by rewrite !fnd_set; case: eqP => // ->; rewrite !not_fnd.
Qed.

End RestrictionOps.

Arguments filterf : simpl never.
Arguments restrictf : simpl never.
Notation "x .[: A ]" := (restrictf x A) : fmap_scope.
Notation "x .[\ A ]" := (x.[: domf x :\: A]) : fmap_scope.
Notation "x .[~ k ]" := (x.[\ [fset k]]) : fmap_scope.

Section Cat.
Variables (K : keyType) (V : Type).
Implicit Types (f g : {fmap K -> V}).

Definition catf (f g : {fmap K -> V}) :=
  FinMap [ffun k : (domf f :\: domf g) :|: domf g=>
          match fsetULVR (valP k) with
            | inl kfDg => f.[fsubsetP (fsubsetDl _ _) _ kfDg]
            | inr kg => g.[kg]
          end].

Local Notation "f + g" := (catf f g) : fset_scope.

Lemma domf_cat f g : domf (f + g) = domf f :|: domf g.
Proof.
by apply/fsetP=> x; rewrite !in_fsetE; case: (boolP (_ \in _)); rewrite ?orbT.
Qed.

Lemma mem_catf f g k : k \in domf (f + g) = (k \in f) || (k \in g).
Proof. by rewrite domf_cat in_fsetE. Qed.

Lemma fnd_cat f g k :
  (f + g).[? k] = if k \in domf g then g.[? k] else f.[? k].
Proof.
rewrite /catf /=; case: fndP => //= [kfg|].
  rewrite ffunE /=; case: fsetULVR => [kf|kg]; last by rewrite -in_fnd kg.
  by rewrite -in_fnd; move: kf; rewrite in_fsetE => /andP[/negPf ->].
by rewrite mem_catf => /norP [kNf kNg]; rewrite !not_fnd // if_same.
Qed.

Lemma catfE f g : f + g = f.[\ domf g] + g.
Proof. by apply/fmapP=> k; rewrite !(fnd_cat, fnd_rem); case: ifP. Qed.

Lemma getf_catl f g k (kfg : k \in domf (f + g))
      (kf : k \in domf f) : k \notin domf g -> (f + g).[kfg] = f.[kf].
Proof.
by move=> kNg; apply: Some_inj; rewrite -in_fnd fnd_cat (negPf kNg) in_fnd.
Qed.

Lemma getf_catr f g k (kfg : k \in domf (f + g))
      (kg : k \in domf g) : (f + g).[kfg] = g.[kg].
Proof. by apply: Some_inj; rewrite -in_fnd fnd_cat kg in_fnd. Qed.

Lemma catf0 f : f + [fmap] = f.
Proof. by apply/fmapP => k; rewrite fnd_cat in_fset0. Qed.

Lemma cat0f f : [fmap] + f = f.
Proof.
by apply/fmapP => k; rewrite fnd_cat; case: ifPn => //= ?; rewrite !not_fnd.
Qed.

Lemma catf_setl f g k (v : V) :
  f.[k <- v] + g = if k \in g then f + g else (f + g).[k <- v].
Proof. (* :BUG: rewrite [fnd ^~ k']fun_if does not work *)
apply/fmapP=> k'; rewrite (fun_if (fnd ^~ k')) !(fnd_cat, fnd_set).
by have [->|Nkk'] := altP eqP; do !case: (_ \in _).
Qed.

Lemma catf_setr f g k (v : V) : f + g.[k <- v] = (f + g).[k <- v].
Proof.
apply/fmapP=> k'; rewrite !(fnd_cat, fnd_set, mem_setf, inE).
by have [->|Nkk'] := altP eqP; do !case: (_ \in _).
Qed.

Lemma restrictf_cat f g A : (f + g).[: A] = f.[: A] + g.[: A].
Proof.
apply/fmapP => k'; rewrite !(fnd_cat, fnd_restrict) mem_restrictf.
by case: (_ \in _).
Qed.

Lemma restrictf_cat_domr f g : (f + g).[: domf g] = g.
Proof.
rewrite catfE restrictf_cat restrictf_comp.
by rewrite fsetIDAC fsetDIl fsetDv fsetI0 restrictf0 restrictfT cat0f.
Qed.

Lemma remf_cat f g A : (f + g).[\ A] = f.[\ A] + g.[\ A].
Proof.
by apply/fmapP => k'; rewrite !(fnd_cat, fnd_rem) mem_remf; case: (_ \in _).
Qed.

Lemma catf_restrictl A f g : f.[: A] + g = (f + g).[: A :|: domf g].
Proof.
apply/fmapP=> k; rewrite !(fnd_cat, fnd_restrict) !in_fsetE.
by do !case: (_ \in _).
Qed.

Lemma catf_reml A f g : f.[\ A] + g = (f + g).[\ A :\: domf g].
Proof.
by apply/fmapP=> k; rewrite !(fnd_cat, fnd_rem) in_fsetE; case: (_ \in _).
Qed.

Lemma catf_rem1l k f g :
  f.[~ k] + g = if k \in g then f + g else (f + g).[~ k].
Proof.
apply/fmapP => k'; rewrite (fun_if (fnd ^~ k')) !(fnd_cat, fnd_rem1).
by have [->|?] := altP eqP; do !case: (_ \in _).
Qed.

Lemma setf_catr f g k (v : V) : (f + g).[k <- v] = f + g.[k <- v].
Proof. by rewrite catf_setr. Qed.

Lemma setf_catl f g k (v : V) : (f + g).[k <- v] = f.[k <- v] + g.[~ k].
Proof. by rewrite catf_setl mem_remf1 eqxx /= !setf_catr setf_rem1. Qed.

Lemma catfA f g h : f + (g + h) = f + g + h.
Proof.
by apply/fmapP => k; rewrite !fnd_cat !mem_catf; do !case: (_ \in _).
Qed.

Lemma catfC f g : f + g = g + f.[\ domf g].
Proof.
apply/fmapP=> k; rewrite !fnd_cat domf_rem in_fsetE /= fnd_rem.
by have [|kNg] //= := boolP (_ \in domf g); rewrite (not_fnd kNg); case: fndP.
Qed.

Lemma disjoint_catfC f g : [disjoint domf f & domf g] -> f + g = g + f.
Proof. by move=> dfg; rewrite catfC remf_id. Qed.

Lemma catfAC f g h : f + g + h = f + h + g.[\ domf h].
Proof. by rewrite -!catfA [X in _ + X]catfC. Qed.

Lemma disjoint_catfAC f g h : [disjoint domf g & domf h]%fmap ->
     f + g + h = f + h + g.
Proof. by move=> dgh; rewrite catfAC remf_id. Qed.

Lemma catfCA f g h : f + (g + h) = g + (f.[\ domf g] + h).
Proof. by rewrite !catfA [X in X + _]catfC. Qed.

Lemma disjoint_catfCA f g h : [disjoint domf f & domf g]%fmap ->
     f + (g + h) = g + (f + h).
Proof. by move=> dfg; rewrite catfCA remf_id. Qed.

Lemma catfIs f g h : f + h = g + h -> f.[\ domf h] = g.[\ domf h].
Proof.
move=> /fmapP eq_fg_fh; apply/fmapP => k; have := eq_fg_fh k.
by rewrite !fnd_cat !fnd_rem; case: ifP.
Qed.

Lemma disjoint_catfIs h f g :
  [disjoint domf f & domf h] -> [disjoint domf g & domf h] ->
  f + h = g + h -> f = g.
Proof. by move=> dfg dgh /catfIs; rewrite !remf_id. Qed.

Lemma restrict_catfsI f g h : f + g = f + h -> g.[: domf h] = h.[: domf g].
Proof.
move=> /fmapP eq_fg_fh; apply/fmapP => k; have := eq_fg_fh k.
rewrite !fnd_cat !fnd_restrict.
by do ![case: (boolP (_ \in _)) => ? //=] => _; rewrite not_fnd.
Qed.

Lemma disjoint_catfsI h f g :
  [disjoint domf f & domf h] -> [disjoint domf g & domf h] ->
  h + f = h + g -> f = g.
Proof.
move=> dfg dgh; rewrite -disjoint_catfC // -[RHS]disjoint_catfC //.
by apply: disjoint_catfIs.
Qed.

End Cat.

Arguments catf : simpl never.
Notation "f + g" := (catf f g) : fset_scope.

Section FinMapEqType.

Variables (K : keyType) (V : eqType).

Let T_ (d : {fset K}) := {ffun d -> V}.
Local Notation finMap' := {d : _ & T_ d}.

Definition finMap_encode (f : {fmap K -> V}) := Tagged T_ (ffun_of_fmap f).
Definition finMap_decode (f : finMap') := FinMap (tagged f).
Lemma finMap_codeK : cancel finMap_encode finMap_decode.
Proof. by case. Qed.

Definition finMap_eqMixin := CanEqMixin finMap_codeK.
Canonical finMap_eqType := EqType {fmap K -> V} finMap_eqMixin.

End FinMapEqType.
