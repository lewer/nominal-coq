From Ssreflect
Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq fintype.

From MathComp
Require Import bigop  finfun finset generic_quotient perm tuple fingroup.

Require Import finmap finsfun finperm utilitaires.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope finperm_scope with fperm.
Local Open Scope finperm_scope.
Local Open Scope fset.
Local Open Scope quotient_scope.

Import Key.Exports.
  
Definition atom := nat_KeyType.
Definition atom_type := keyType.

Axiom funext : forall {X : Type} {I : finType} (f g : I -> X),
                 f =1 g -> f = g.

Section NominalDef.

Record perm_setoid_mixin (X : Type) (R : X -> X -> Prop) (A : atom_type)
  := PermSetoidMixin {
  act : {finperm A } -> X -> X;
  _ : forall x, R ((act (1 A)) x) x;
  _ : forall π π' x, R (act (π * π') x) (act π (act π' x));
  _ : forall x y π, R x y -> R (act π x) (act π y)
}.

Record nominal_mixin (X : choiceType) (A : atom_type) := NominalMixin {
  perm_setoid_of : @perm_setoid_mixin X (@eq X) A;
  supp : X -> {fset A}; 
  _ : forall (π : {finperm A}) x, 
        (forall a : A, a \in supp x -> π a = a) -> (act perm_setoid_of π x) = x
}.
                                    
Record nominalType (A : atom_type) := NominalType {
                           car :> choiceType;
                           nominal_mix : nominal_mixin car A}.

Definition actN A (nt : nominalType A) := act (perm_setoid_of (nominal_mix nt)).

End NominalDef.

Notation "π \dot x" := (@actN _ _ π x)
                         (x at level 60, at level 60).
Notation swap := tfinperm.

Section BasicNominalTheory.

Variables (A : atom_type) (W X Y Z : nominalType A).
Implicit Types (π : {finperm A}) (x : X).

Local Notation act π := (@actN A X π).
Local Notation support := (supp (nominal_mix X)).

Lemma act1 : act (1 A) =1 id.
Proof. by case: X => car; case; case. Qed.

Lemma actM (π1 π2 : {finperm A}) : forall x : X,  (π1 * π2) \dot x = π1 \dot (π2 \dot x).
Proof. by case: X => car; case; case. Qed.

Lemma act_id π : forall x : X, (forall a : A, a \in support x -> π a = a) 
                   -> (act π x) = x.
Proof. case: X => car. case => ps supp. exact. Qed.

Lemma actK π : cancel (act π) (act π^-1).
Proof. by move => x; rewrite -actM (finperm_invP π) act1. Qed.

Lemma actVK π : cancel (act π^-1) (act π).
Proof. by move => x; rewrite -actM (finperm_invVP π) act1. Qed.

Lemma act_inj π : injective (act π).
Proof. by move => x y /(congr1 (act π^-1)); rewrite !actK. Qed.

Lemma act_conj π a b x : π \dot (swap a b) \dot x = swap (π a) (π b) \dot π \dot x.
Proof. by rewrite -!actM tfinperm_conj. Qed.

Lemma act_conj_imL π a b x : π \dot (swap a (π^-1 b)) \dot x = swap (π a) b \dot π \dot x.
Proof. by rewrite -!actM tfinperm_conj_imL. Qed.

Lemma act_conj_imR π a b x : π \dot (swap (π^-1 a) b) \dot x = swap a (π b) \dot π \dot x.
Proof. by rewrite -!actM tfinperm_conj_imR. Qed.

End BasicNominalTheory.

Definition support A (nt : nominalType A) x := supp (nominal_mix nt) x.

Section NominalTrivial.

Variables (A : atom_type) (X : choiceType).
  
Definition trivialact (π : {finperm A}) (x : X) := x.

Lemma trivialact1 : forall x, trivialact (1 A) x = x.
Proof. by []. Qed.

Lemma trivialactM π π' x : trivialact (π * π') x = trivialact π (trivialact π' x).
Proof. by []. Qed.

Lemma trivialactproper x y π : x = y -> (trivialact π x) = (trivialact π y).
Proof.  by move ->. Qed.

Definition trivial_nominal_setoid_mixin :=
  @PermSetoidMixin X (@eq X) A trivialact trivialact1 trivialactM trivialactproper.

Lemma trivialact_id (π : {finperm A})  x :
  (forall a, a \in fset0 -> π a = a) -> trivialact π x = x.
Proof. by []. Qed.

Canonical trivial_nominal_mixin :=
  @NominalMixin X A trivial_nominal_setoid_mixin _ trivialact_id.

Canonical trivial_nominal_type :=
  NominalType trivial_nominal_mixin.

Lemma trivialactE π x : trivialact π x = x.
Proof. by []. Qed.

End NominalTrivial.

Section NominalList.

Variables (A : atom_type) (X : nominalType A).

Definition listact π (l : seq X) := map (@actN _ X π) l.

Lemma listact1 l : listact (1 A) l = l.
Proof.
elim: l => //= a l IHl. by rewrite act1 IHl.
Qed.

Lemma listactM π π' l : listact (π * π') l = listact π (listact π' l).
Proof.
elim: l => //= a l IHl. by rewrite actM IHl.
Qed.  

Lemma listactproper l1 l2 π : l1 = l2 -> listact π l1 = listact π l2.
Proof. by move ->. Qed.

Definition list_nominal_setoid_mixin := 
  @PermSetoidMixin (seq X) (@eq (seq X)) A listact listact1 listactM listactproper.   

Definition list_support (l : seq X) := fsetU_list [seq support x | x <- l].

Lemma listact_id (π : {finperm A}) l :
  (forall a, a \in list_support l -> π a = a) -> listact π l = l.
Proof. 
elim: l => //= x l IHl Hal.
rewrite IHl => [|a a_supp_l].
  rewrite act_id //= => a a_supp_x.
  apply Hal. by rewrite /list_support/= in_fsetU a_supp_x.
apply Hal. by rewrite /list_support /= in_fsetU a_supp_l orbT.
Qed.

Canonical list_nominal_mixin :=
  @NominalMixin _ A list_nominal_setoid_mixin _ listact_id.

Canonical list_nominal_type :=
  NominalType list_nominal_mixin.

Lemma listactE π (l : seq X) : π \dot l = [seq π \dot x | x <- l].
Proof. by []. Qed.

Lemma cons_support (l : seq X) (x : X) : 
  list_support (x :: l) = (support x) `|` (list_support l).
Proof. by []. Qed.

(* Lemma mem_support (l : seq X) (t : X) : *)
(*   t \in l -> support t `<=` support l. *)
(* Proof. *)
(* elim: l => [|u l IHl]. *)
(*   by rewrite in_nil. *)
(* rewrite in_cons => /orP. case. *)
(*   move => /eqP -> /=.  *)

End NominalList.

Section NominalProd.

Variables (A : atom_type) (X Y : nominalType A).
Implicit Type (x : X * Y).

Definition prodact π x := (π \dot x.1, π \dot x.2).

Lemma prodact1 : forall x, prodact (1 A) x = x.
Proof. by case => x y; rewrite /prodact !act1. Qed.

Lemma prodactM π π' : forall x, prodact (π * π') x = prodact π (prodact π' x).
Proof. by case => x y /=; rewrite /prodact !actM. Qed.

Lemma prodactproper : forall x y π, x = y -> (prodact π x) = (prodact π y).
Proof. by move => x y π ->. Qed.

Definition prod_nominal_setoid_mixin := 
  @PermSetoidMixin (X * Y) (@eq (X * Y)) A prodact prodact1 prodactM prodactproper.   

Lemma prodact_id (π : {finperm A}) x :
     (forall a, a \in (support x.1 `|` support x.2) -> π a = a) -> prodact π x = x.
Proof. 
case: x => x y Hsupp. rewrite /prodact !act_id //= => a asupp; apply Hsupp;
rewrite in_fsetU asupp ?orbT //.
Qed.

Canonical prod_nominal_mixin :=
  @NominalMixin _ A prod_nominal_setoid_mixin _ prodact_id.

Canonical prod_nominal_type :=
  NominalType prod_nominal_mixin.

Lemma prodactE π (y : X) (z : Y) : π \dot (y, z) = (π \dot y, π \dot z).
Proof. by []. Qed.

End NominalProd.

(* Lemma strong_prodctsupport π a : *)
(*   atomact π a = a -> (forall b, b \in fset1 a -> atomact π b = b). *)
(* Proof. move => /= πa_eq_a b. by rewrite in_fset1 => /eqP ->. Qed. *)


Section NominalAtoms.

Implicit Types (π : {finperm atom}) (a : atom).

Definition atomact π a := π a.

Lemma atomact1 : forall (a : atom), atomact (1 atom) a = a.
Proof. by move => a /=; rewrite /atomact finsfun1. Qed.

Lemma atomactM : forall π π' a, atomact (π * π') a = atomact π (atomact π' a).
Proof. by move => π π' a /=; rewrite /atomact finsfunM. Qed.

Lemma atomactproper : forall x y π, x = y -> (atomact π x) = (atomact π y).
Proof. by move => x y π ->. Qed.

Definition atom_nominal_setoid_mixin := 
  @PermSetoidMixin _ (@eq atom) atom atomact atomact1 atomactM atomactproper.   

Lemma atomact_id π a :
     (forall b, b \in fset1 a -> atomact π b = b) -> atomact π a = a.
Proof. apply. by rewrite in_fset1. Qed.

Lemma strong_atomactsupport π a :
  atomact π a = a -> (forall b, b \in fset1 a -> atomact π b = b).
Proof. move => /= πa_eq_a b. by rewrite in_fset1 => /eqP ->. Qed.

Canonical atom_nominal_mixin :=
  @NominalMixin _ atom atom_nominal_setoid_mixin _ atomact_id.

Canonical atom_nominal_type :=
  @NominalType atom nat_choiceType atom_nominal_mixin.

Lemma swapL a b : (swap a b) \dot a = b. 
Proof. by rewrite /actN /= /atomact tfinpermL. Qed.

Lemma swapR a b : (swap a b) \dot b = a.
Proof. by rewrite /actN /= /atomact tfinpermR. Qed.

Lemma atomactE π a : π \dot a = π a.
Proof. by []. Qed.

End NominalAtoms.

Section NominalAtomSubsets.

Implicit Types (π : {finperm atom}) (A : {fset atom}).

Definition ssatomact π A := im π A. 

Lemma ssatomact1 : forall A, ssatomact (1 atom) A = A.
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

Definition ssatom_nominal_setoid_mixin := 
  @PermSetoidMixin {fset atom} (@eq {fset atom}) atom ssatomact ssatomact1 ssatomactM ssatomactproper. 

Canonical ssatom_nominal_mixin :=
  @NominalMixin finset_choiceType atom ssatom_nominal_setoid_mixin _ ssatomact_id.

Canonical ssatom_nominal_type :=
  @NominalType atom finset_choiceType ssatom_nominal_mixin. 

Lemma mem_imperm π A (a : atom) : (π a \in π \dot A) = (a \in A).
Proof. by apply/mem_im/finperm_inj. Qed.

End NominalAtomSubsets. 

Section Nominalffun.

Context (X : nominalType atom) (I : finType).

Definition ffunact π (f : {ffun I -> X}) := [ffun i => π \dot f i].

Lemma ffunact1 : ffunact (1 atom) =1 id.
Proof.
move => f /=.
apply/ffunP => i.
by rewrite ffunE act1.
Qed.

Lemma ffunactM : forall π π' f, ffunact (π * π') f = ffunact π (ffunact π' f).
Proof.
move => π π' f /=. 
apply/ffunP => i.
by rewrite !ffunE actM.
Qed.

Lemma ffunactproper (f g : {ffun I -> X}) π : f = g -> (ffunact π f) = (ffunact π g).
Proof. by move => ->. Qed.

Lemma ffunact_id (π : {finperm atom}) (f : {ffun I -> X}) :
  (forall b, b \in (\fbigcup_(i in I) (support (f i))) -> π b = b) -> ffunact π f = f.
Proof.
move => fsupp /=.
apply/ffunP => i.
rewrite ffunE. apply/act_id => a a_supp_fi.
apply/fsupp/fbigcupP. by exists i.
Qed.

Definition ffun_nominal_setoid_mixin :=
  @PermSetoidMixin _ (@eq {ffun I -> X}) atom ffunact ffunact1 ffunactM ffunactproper.

Canonical ffun_nominal_mixin :=
  @NominalMixin (finfun_choiceType I X) atom ffun_nominal_setoid_mixin _ ffunact_id.

Canonical ffun_nominal_type :=
  @NominalType atom (finfun_choiceType I X) ffun_nominal_mixin.

End Nominalffun.

Section Freshness.

Implicit Types (X Y: nominalType atom).

Definition max (A : {fset atom}) := \max_(a : A) val a. 

Definition fresh_in X (x : X) := (max (support x)).+1. 

Definition supports X (A : {fset atom}) (x : X) := 
  forall (π : {finperm atom}), (forall a : atom, a \in A -> π a = a) -> π \dot x = x.

Lemma supportsP (X : nominalType atom) (x : X) :
  supports (support x) x.
Proof.
move => π. 
exact: act_id.
Qed.

Lemma in_le_max x (A : {fset atom}) : x \in A -> x <= max A.
Proof.
Admitted.

Lemma fresh_notin (A : {fset atom}) : (fresh_in A) \notin A.
Proof.
  rewrite /fresh_in /support /=.
  have bounded: forall x, x \in A -> x != (max A).+1.
  move=> x xinA. rewrite neq_ltn. apply/orP.
  apply: or_introl. by apply: in_le_max.
  apply/memPn; apply: bounded.
Qed.

Lemma fresh_neq_in (A : {fset atom}) a : a \in A -> a != fresh_in A.
Proof. apply contraL => /eqP ->. exact: fresh_notin. Qed.

Lemma fresh_neq x : x != fresh_in x.
Proof. rewrite/fresh_in/support/=.
Admitted.
       
Lemma supports_fsetP (A B  : {fset atom}) : reflect (supports A B) (B `<=` A).
Proof.
apply: (iffP idP) =>[/fsubsetP B_sub_A π fix_A|A_supp_B].
  apply ssatomact_id => b /B_sub_A. exact: (fix_A b).
apply/fsubsetP => a aB.
apply contraT => aNA.
have a_fAB : swap a (fresh_in (A, B)) \dot B = B.
apply A_supp_B => b bA. apply/tfinpermNone/andP. split.
  apply/eqP => H; subst; by rewrite bA in aNA.
  have : b \in A `|` B by rewrite in_fsetU bA.
    exact: fresh_neq_in.
have : fresh_in (A, B) \in A `|` B.
  rewrite in_fsetU; apply /orP; right.
  by rewrite -(tfinpermL a (fresh_in (A, B))) -{2}a_fAB ?mem_imperm.
by move/fresh_neq_in/eqP.
Qed.

Lemma supportsI (X : nominalType atom) (A B : {fset atom}) (x : X) : 
  supports A x -> supports B x -> supports (A `&` B) x. 
Proof.
(* suppose le théorème de décomposition des permutations en 
   produit de transpositions *)
Admitted.


Definition fresh X a (x : X) := exists (S : {fset atom}), a \notin S /\ supports S x. 

Notation "a # x" := (fresh a x) (x at level 60, at level 60).

Lemma fresh1P X (x : X) : (fresh_in x) # x.
Proof.
exists (support x).
split.
  exact: fresh_notin.
exact: supportsP.
Qed.

Lemma fresh_equiv (X : nominalType atom) (x : X) a (π : {finperm atom}) : 
  (a # x) <-> (π a) # (π \dot x). 
Proof.
wlog suff : x π a / a # x -> (π a) # (π \dot x) => Hsuff. 
  split; first by apply Hsuff.
  rewrite -{2}[a](finpermK π) -{2}[x](actK π).
  exact: Hsuff.
move : Hsuff => [S] [aNS supp_S_x].
exists (π \dot S). split; first by rewrite mem_imperm.
move => Ɣ HƔ. apply (@act_inj _ _ π^-1). rewrite actK -2?actM.  
apply supp_S_x => b bS. rewrite finsfunM /= finsfunM /= HƔ;
  first exact: finpermK.
by rewrite mem_imperm.
Qed.

Lemma im_fresh (X : nominalType atom) (π : {finperm atom}) a (x : X) :
  a # (π^-1 \dot x) -> (π a) # x.
Proof. by rewrite -{2}[x](actVK π); apply fresh_equiv. Qed.

Lemma im_inv_fresh (X : nominalType atom) (π : {finperm atom}) a (x : X) :
  a # (π \dot x) -> (π^-1 a) # x.
Proof. rewrite -{2}[x](actK π). by apply fresh_equiv. Qed.

Lemma CFN_principle b {X : nominalType atom} {a} {x : X} :
  b # x -> swap a b \dot x = x -> a # x.
Proof.
move => bFx abx_eq_x.
apply (@fresh_equiv _ _ _ (swap a b)).
by rewrite tfinpermL abx_eq_x.
Qed.

Lemma fresh_atomP x y : reflect (x # y) (x != y). 
Proof.
apply: (iffP idP) => [xNy| [S] [xNS S_supp_y]].
  apply (@CFN_principle (fresh_in y)); first exact: fresh1P.
  apply/tfinpermNone/andP; split; first by rewrite eq_sym.
  exact: fresh_neq.  
apply/negP => /eqP x_eq_y.
rewrite -x_eq_y in S_supp_y.
have : forall a, a \notin S -> a = x.
  move => a aNS. rewrite -(tfinpermR a x). apply S_supp_y => b bS.
  apply/tfinpermNone/andP; split; apply/eqP => H; subst.
    by rewrite bS in aNS.
  by rewrite bS in xNS.  
have freshxSNS : (fresh_in (x |` S)) \notin S.
  move: (fresh_notin (support x `|` S)).
  by rewrite in_fset1U negb_or => /andP; case. 
move/(_ (fresh_in (x |` S))) /(_ freshxSNS).
move: (fresh_neq_in (fset1U1 x S)).
by rewrite eq_sym => /eqP. 
Qed.

Lemma fresh_atomC x y : x # y <-> y # x.
Proof.
split => hFresh .
all: apply/fresh_atomP.
all: rewrite eq_sym.
all: by apply/fresh_atomP.
Qed.

Lemma fresh_fsetP (A : {fset atom}) x : reflect (x # A) (x \notin A).
Proof.
apply: (iffP idP) => [xNA|[S] [xNS /supports_fsetP /fsubsetP S_supp_A ]].
  exists A. split => //. exact: supportsP.
exact: (contra (S_supp_A x)).
Qed.

Lemma fresh_fsetU1 (A B : {fset atom}) x : x # (A `|` B) -> x # A.
Proof.
move/fresh_fsetP.
rewrite in_fsetU negb_or => /andP [? _].
exact/fresh_fsetP.
Qed.

Lemma fresh_fsetU2 (A B : {fset atom}) x : x # (A `|` B) -> x # B.
Proof.
move/fresh_fsetP.
rewrite in_fsetU negb_or => /andP [_ ?].
exact/fresh_fsetP.
Qed.

Lemma fresh_support X a (x : X) : a \notin (support x) -> a # x.
Proof.
move => aNx. exists (support x).
split => //.
exact: supportsP.
Qed.

Lemma act_fresh {X : nominalType atom} (a b : atom) (x : X) :
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

Lemma fresh_prod X Y a (x : X) (y : Y) : a # (x, y) <-> (a # x) /\ (a # y). 
Proof.
split.
  move => [S] [aNS supp_S_xy].
  split; exists S; split => //; move => π /(supp_S_xy π); rewrite prodactE.
    by move/(congr1 fst).
  by move/(congr1 snd).
move => [[Sx] [aNSx supp_Sx_x] [Sy] [aNSy supp_Sy_y]].
exists (Sx `|` Sy); split.
  by rewrite in_fsetU negb_or aNSx aNSy.
move => π H. rewrite prodactE.
have -> : π \dot x = x.
  apply (supp_Sx_x π) => b bSx. apply H.
  by rewrite in_fsetU bSx. 
suff : π \dot y = y by move ->.
apply (supp_Sy_y π) => b bSy. apply H.
  by rewrite in_fsetU bSy orbT.
Qed.

Lemma fresh_nil {X} a : a # Nil X.
Proof.
exists fset0. split => //.
by rewrite in_fset0.
Qed.

Lemma supports_cons {X} S (x : X) (l : seq X): 
  supports S (x :: l) -> supports S x /\ supports S l.
Proof.
move => S_supp_xl.
split => π HS.
all: move : (S_supp_xl π HS) => /= /eqP.
all: by rewrite !listactE /= eqseq_cons => /andP [/eqP ? /eqP ?]. 
Qed.

Lemma fresh_cons {X} (l : seq X) a x : a # (x :: l) <-> a # x /\ a # l.
Proof.
split.
  move => [S] [aNS /supports_cons [S_supp_x S_supp_l]]. 
  split; by exists S; split => //. 
move => [[Sa] [aNSa Sa_supp_x] [Sl] [aNSl Sl_supp_l]].
exists (Sa `|` Sl); split.
  by rewrite in_fsetU negb_or aNSa aNSl.
move => π H. 
Admitted.

Lemma fresh_list {X} (l : seq X) a : a # l <-> forall x, x \in l -> a # x.
Proof. 
elim: l => [|b l IH]. 
  split => // ?; exact/fresh_nil.
split => [/fresh_cons [aFb aFl] y|Hbl]. 
   rewrite inE => /orP. case.
    by move /eqP ->.
  exact/(iffLR IH aFl).
apply fresh_cons; split.
  exact/Hbl/mem_head.
apply IH => x xl; apply/Hbl.
by rewrite in_cons xl orbT.
Qed.

Lemma fresh_map {T : finType} {X : nominalType atom} (f : T -> X) a :
  a # [seq f i | i : T] -> forall i, a # f i.
Proof.
move/fresh_list => H i.
exact/H/map_f/mem_enum. 
Qed.

Lemma fresh_perm (X : nominalType atom) (π : {finperm atom}) (x : X) : 
  [disjoint (support x) & finsupp π] -> π \dot x = x.
Proof.
move => /fdisjointP disj_x_π.  
apply act_id => a /disj_x_π.
exact: finsfun_dflt.
Qed.

Lemma tfinperm_fresh a b c : a # c -> b # c -> swap a b c = c.
Proof.
move => aFc bFc.
apply/tfinpermNone/andP; split.
all: exact/fresh_atomP/fresh_atomC.
Qed.

Lemma disjoint_tfsupp a b S :
  a # S -> b # S -> [disjoint finsupp (swap a b) & S].
Proof.
move => aFS bFS. rewrite fdisjoint_sym.
by apply/tfinperm_disj; exact/fresh_fsetP.
Qed.

Lemma disjoint_conj (π π' : {finperm atom}) T :
  [disjoint finsupp π & T] -> [disjoint finsupp π' & T] ->
  [disjoint finsupp (π * π') & T].
Proof.
move => /fdisjointP disj_pi_T /fdisjointP disj_pi'_T.
apply/fdisjointP => a /(fsubsetP (finsupp_conj π' π) a).
by rewrite in_fsetU => /orP [?|?]; auto.
Qed.

Lemma disj_im_fresh (π : {finperm atom}) T x : 
  [disjoint finsupp π & T] -> x # T -> π x # T.
Proof.
move => /fdisjointP disj_pi_T xFT.
have [/eqP ->|pix_neq_x] := boolP (π x == x) => //.
have : π (π x) != π x.
  apply/negP => /eqP/finperm_inj.
  by move: pix_neq_x => /eqP.
by rewrite -mem_finsupp => /disj_pi_T /fresh_fsetP.
Qed.
  
End Freshness.

Notation "a # x" := (fresh a x) (x at level 60, at level 60).

Ltac freshTac :=
  match goal with
    | |- (fresh_in ?x) # ?x => apply fresh1P
    | |- ?a # ?x =>
      try (subst a);
      match goal with
        | |- fresh_in ?y  # ?x => move : (fresh1P y)
      end;
      repeat (move/fresh_prod; case)
  end; move => *.
        

Ltac freshTacCtxt z :=
  match goal with
      | [ y := fresh_in ?x |- _] => 
        match y with
          |z => move: (fresh1P x); rewrite -/z
        end
  end;
  repeat 
    (move/fresh_prod;
     case);
  move => *.

Ltac freshTacList :=
  match goal with
  | |- ?z # ?t  => 
    match goal with 
      | [ H : is_true (t \in ?l) |- _] => apply (@fresh_list _ l) => //
    end
end.
      

(* fresh_dec (e : list { X : nominalType & X }) nom : is_fresh_dec x y -> is_fresh (fresh_in (interp e x)) (interp e y) *)
(* Hint Extern 0 (@is_fresh _ _ _) => eapply fresh_in_fresh : typeclass_instances. *)
(*Hint Mode is_fresh + - - : typeclass_instances.*)

Section EquivariantFunctions.

Implicit Types (W X Y Z: nominalType atom) (π : {finperm atom}).

Definition equivariant1 X Y (f : X -> Y) := forall π x, f (π \dot x) = π \dot (f x). 

Definition equivariant2 X Y Z (f : X -> Y -> Z) := 
  forall π x y,  f (π \dot x) (π \dot y) = π \dot (f x y).

Definition equivariant3 X Y Z W (f :  X -> Y -> Z -> W) :=
  forall π x y z, f (π \dot x) (π \dot y) (π \dot z) = π \dot (f x y z).

Definition equivariant_prop X Y (R : X -> Y -> Prop) :=
  forall π x y, R (π \dot x) (π \dot y) <-> R x y.

Lemma all2_equivariant {A : nominalType atom} (s1 s2 : seq A) (p : A -> A -> bool) π :
  equivariant2 p -> 
  all2 p (π \dot s1) (π \dot s2) = all2 p s1 s2.  
Proof.
move => p_equi.
rewrite all2_map. apply all2_eq => x y.
exact/p_equi.
Qed. 

Lemma map_equivariant {A B : nominalType atom} (f : A -> B) l π : 
  (forall x, x \in l -> π \dot f x = f (π \dot x)) ->
   π \dot (map f l) = map f (π \dot l).
Proof.  
move => f_equiv.
rewrite listactE -!map_comp. 
apply eq_in_map => t tl /=.
exact/f_equiv.
Qed.

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

(* Section FinitelySupportedFunctions. *)

(* Implicit Types (V W X Y Z : nominalType atom) (π : {finperm atom}) (S : {fset atom}). *)

(* Definition fsupports1 {X Y} (f : X -> Y) S := *)
(*   forall a b x, (swap a b) \dot (f x) = f (swap a b \dot x). *)

(* Definition finitely_supported1 X Y (f : X -> Y) := *)
(*   exists S, fsupports1 f S. *)

(* Definition fsupports2 X Y Z (f : X -> Y -> Z) S := *)
(*    forall a b x y, swap a b \dot (f x y) = *)
(*                    f (swap a b \dot x) (swap a b \dot y). *)

(* Definition finitely_supported2 X Y Z (f : X -> Y -> Z) := *)
(*   exists S, fsupports2 f S. *)

(* Definition fsupports *)

(* Definition function_support *)

(* End FinitelySupportedFunctions. *)

(* Section StrongSupport. *)

(* Variables (X : nominalType) (S : {fset atom}). *)
(* Implicit Types (x : X). *)

(* (* (* hypothèse qui implique que S est le plus petit support de x *) *) *)
(* (* Hypothesis strong_support :  *) *)
(* (*   forall x π, π \dot x = x -> (forall a : atom, a \in (support x) -> π a == a). *) *)

(* (* Lemma equi_support : equivariant1 (@support X). *) *)
(* (* Proof. *) *)
(* (* move => π x. *) *)
(* (* wlog suff : x π / im π (support x) `<=` support (π \dot x). *) *)
(* (*   move => Hsuff; apply/eqP; rewrite eqEfsubset; apply/andP; split; last by apply Hsuff. *) *)
(* (*   rewrite -(actVK π (support (π \dot x))) -{2}[x](actK π x); *) *)
(* (*   exact/im_subset/Hsuff. *) *)
(* (* apply/fsubsetP => a /imfsetP [b bx] ->. apply contraT => πbNπx. *) *)
(* (* set c := fresh_in (val b, im π^-1 (support (π \dot x))). *) *)
(* (* have : swap (val b) c \dot x = x. *) *)
(* (*   apply (@act_inj _ π). rewrite -actM tfinperm_conj actM act_fresh //. *) *)
(* (*     exact: fresh_support πbNπx. *) *)
(* (*   exists (support (π \dot x)). *) *)
(* (*   split; last exact: supportsP. *) *)
(* (*   rewrite -(actVK π (support (π \dot x))) mem_im. *) *)
(* (*     by admit.   *) *)
(* (*   exact: finperm_inj. *) *)
(* (* have {bx} bx : val b \in support x. by apply valP. *) *)
(* (* move/strong_support => H. move: (H (val b) bx). *) *)
(* (* rewrite tfinpermL => /eqP cvalb.  *) *)
(* (* Admitted. *) *)


(* End StrongSupport. *)

Section SomeAny.

Implicit Type (X : nominalType atom).

Definition new (P : atom -> Prop) :=
  exists A : {fset atom}, forall a, a # A -> P a.

Notation "\new a , P" := (new (fun a : nat => P))
   (format "\new  a ,  P", at level 10).
Notation "a # x" := (fresh a x) (x at level 60, at level 60).

Theorem some_any X (R : atom -> X -> Prop) :
  equivariant_prop R ->
  forall x : X, [/\
      (forall a : atom , a # x -> R a x) -> (\new a, (R a x)),
      (\new a, (R a x)) ->  R (fresh_in (support x)) x,
      R (fresh_in (support x)) x -> (exists2 a, a # x & R a x) &
      (exists2 a, a # x & R a x)
      -> (forall a, a # x -> R a x)
    ].
Proof.
move => Requi; split. 
  - exists (support x) => a /fresh_fsetP/fresh_support. exact: (H a).
  - move => [S aNSR].
    apply/(Requi (swap (fresh_in x) (fresh_in (x,S)))).
    rewrite swapL [_ \dot x]act_fresh; try (by freshTac). 
    apply/aNSR. by freshTac.
  - move => Rfresh. exists (fresh_in x) => //. exact: fresh1P.
  - move => [a a_fresh_x rax] a' a'_fresh_x.
    rewrite -[a'](tfinpermL a a') -[x](@act_fresh _ a a') //. 
    by apply/Requi.
Qed.

Lemma new_forall X (R : atom -> X -> Prop) :
  equivariant_prop R ->
  forall x : X, ((\new a, (R a x)) <-> (forall a, a # x -> R a x)).
Proof.
move=> Requi x. have [? ne ef] := some_any Requi x. 
by split => // /ne /ef.
Qed.

Lemma new_exists X (R : atom -> X -> Prop) :
  equivariant_prop R -> 
  forall x : X, ((\new a, (R a x)) <-> (exists2 a, a # x & R a x)).
Proof.
move=> Requi x; have [fn nf nh ef] := some_any Requi x.
by split => [/nf/nh|/ef].
Qed.

Lemma fresh_new X (R : atom -> X -> Prop) :
  equivariant_prop R ->
  forall x: X, R (fresh_in x) x <-> \new a, (R a x). 
Proof.
move=> Requi x. have [fn nf nh ef] := some_any Requi x. 
by split => [/nh/ef/fn | /nf]. 
Qed.

Lemma some_fresh_new X (R : atom -> X -> Prop) :
  equivariant_prop R ->
  forall (y : atom) (x : X), y # x -> (R y x) <-> \new a, (R a x).
Proof.  
move => Requi y x yFx.
split => [Ryx|/(new_forall Requi) new_Rax].
  apply new_exists => //.
  by exists y.
exact/new_Rax.
Qed.

Lemma new_eq P1 P2 :
 (forall z, P1 z <-> P2 z) -> (\new z, (P1 z)) <-> (\new z, (P2 z)).
Proof.
move => P1_eq_P2.
split.
all: move => [S] HS; exists S => a aFS.
all: exact/P1_eq_P2/(HS _ aFS).
Qed.

Lemma new_all {Y : finType} (P : Y -> atom -> Prop) :
  \new z, (forall y, P y z) <-> forall y, \new z, (P y z).
Proof.
split.
  move => [S] HS y.
  exists S => a aFS.
  exact/HS.
move/fin_all_exists => [Supp] HSupp.
exists (\fbigcup_(y in Y) (Supp y)) => a aFSuppy y.
apply HSupp.
Admitted.

Lemma new_and P1 P2 : 
  \new z, (P1 z /\ P2 z) <-> (\new z, (P1 z) /\ \new z, (P2 z)).
Proof.
split.
  move => [S] HS; split;
  exists S => a aFS. 
    exact: (proj1 (HS _ aFS)).
  exact: (proj2 (HS _ aFS)).
move => [[S1] HS1 [S2] HS2].
exists (S1 `|` S2) => a aFS1S2; split.
  exact/(HS1 a)/(fresh_fsetU1 aFS1S2).
exact/(HS2 a)/(fresh_fsetU2 aFS1S2).
Qed.

Lemma new_andb P1 P2 : 
  \new z, (P1 z && P2 z) <-> (\new z, (P1 z) /\ \new z, (P2 z)).
Proof.
have andb_eq_and : \new z, (P1 z && P2 z) <-> \new z, (P1 z /\ P2 z).
  apply new_eq; split => [/andP|? ] //; exact/andP.
split.
  move/andb_eq_and. by apply new_and.
move => ?. exact/andb_eq_and/new_and.
Qed.


Lemma new_all2 {A : eqType} {p : atom -> A -> A -> bool} {l1 l2 : seq A} : 
  (\new z, (all2 (p z) l1 l2)) <-> (all2_prop (fun t1 t2 => \new z, (p z t1 t2)) l1 l2).
Proof.
elim: l1 l2 => /=.
  move => [|a l2]; split => //.
    by move => _; exists fset0 => //.
  by move => [S] /(_ _ (fresh1P S)).
move => a1 l1 IHl1 [|a2 l2].
  split => //. by move => [S] /(_ _ (fresh1P S)).
split. 
  move/new_andb => [? ?]; split => //.
  by apply/IHl1.
move => [? ?]; apply/new_andb; split => //.
by apply/IHl1.
Qed.


End SomeAny.

Notation "\new a , P" := (new (fun a : nat => P))
   (format "\new  a ,  P", at level 10).
Notation "a # x" := (fresh a x) (x at level 60, at level 60).
