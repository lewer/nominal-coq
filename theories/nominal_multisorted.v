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

Definition atom := nat.

Section NominalDef.

Variables (A : keyType) (asort : finType).

Record perm_setoid_mixin_of (X : Type) (R : X -> X -> Prop) :=
  PermSetoidMixin {
  act_op : asort -> {finperm A} -> X -> X;
  _ : forall aso x, R ((act_op aso 1) x) x;
  _ : forall aso π π' x, R (act_op aso (π * π') x) (act_op aso π (act_op aso π' x));
  _ : forall aso x y π, R x y -> R (act_op aso π x) (act_op aso π y)
}.

Definition pfixe (π : {finperm A}) (B : {fset A}) := 
  forall a, a \in B -> π a = a. 

Record nominal_mixin_of (X : Type) := NominalMixin {
  perm_setoid_mixin :> @perm_setoid_mixin_of X (@eq X);
  support_op : asort -> X -> {fset A};
  _ : forall aso (π : {finperm A}) x,
        pfixe π (support_op aso x) ->
        (act_op perm_setoid_mixin aso π x) = x
}.

Record nominal_class_of (X : Type) := NominalClass {
  nominal_choice_mixin :> @Choice.class_of X;
  nominal_mixin :> @nominal_mixin_of X
}.

Structure nominalType (phA : phant A) := NominalPack {
  nominal_sort :> Type;
  nominal_class : nominal_class_of nominal_sort;
  _ : Type
}.
Local Notation "{nominalType}" := (nominalType (Phant A)).

Variables (T : Type) (cT : {nominalType}).

Definition act := act_op (nominal_class cT).
Definition support := support_op (nominal_class cT).

Definition nominal_pack (phA : phant A) m :=
  fun bT b & phant_id (Choice.class bT) b =>
  @NominalPack phA T (@NominalClass T b m) T.

Definition nominal_clone c of phant_id nominal_class c :=
  @NominalPack (Phant A) T c T.
Let nominal_xT := let: NominalPack T _ _ := cT in T.
Notation nominal_xclass := (@nominal_class (Phant A) cT : nominal_class_of nominal_xT).

Canonical nominal_eqType := @Equality.Pack cT nominal_xclass nominal_xT.
Canonical nominal_choiceType := @Choice.Pack cT nominal_xclass nominal_xT.

End NominalDef.

Coercion nominal_eqType : nominalType >-> Equality.type.
Coercion nominal_choiceType : nominalType >-> Choice.type.

Notation NominalType A asort T m := (@nominal_pack _ asort T (Phant A) m _ _ id).
Notation "{nominalType  A  asort }" := (@nominalType _ asort (Phant A)).

Notation "π \dot_( aso ) x" := (@act _ _ _ aso π x)
                         (x at level 60, at level 60).
Notation swap := tfinperm.

Section BasicNominalTheory.

Context (A : keyType) (asort : finType) (aso : asort)
        (W X Y Z : @nominalType _ asort (Phant A)).
Implicit Types (π : {finperm A}) (x : X).

Local Notation actX := (@act A asort X aso).

Lemma act1 : actX 1 =1 id.
Proof.  by case: X => ? [? [[]]] *. Qed.

Lemma actM (π1 π2 : {finperm A}) : 
  forall x : X,  (π1 * π2) \dot_(aso) x = π1 \dot_(aso) (π2 \dot_(aso) x).
Proof. by case: X => ? [? [[]]]. Qed.

Lemma act_id : forall π (x : X), pfixe π (support aso x)
                   -> π \dot_(aso) x = x.
Proof. by case: X => ? [? [] ? ? H ? ? ? /H]. Qed.

Lemma actK π : cancel (actX π) (actX π^-1).
Proof. by move => x; rewrite -actM (finperm_invP π) act1. Qed.

Lemma actVK π : cancel (actX π^-1) (actX π).
Proof. by move => x; rewrite -actM (finperm_invVP π) act1. Qed.

Lemma act_inj π : injective (actX π).
Proof. by move => x y /(congr1 (act aso π^-1)); rewrite !actK. Qed.

Lemma act_conj π a b x : 
  π \dot_(aso) (swap a b) \dot_(aso) x = swap (π a) (π b) \dot_(aso) π \dot_(aso) x.
Proof. by rewrite -!actM tfinperm_conj. Qed.

Lemma act_conj_imL π a b x : π \dot_(aso) (swap a (π^-1 b)) \dot_(aso) x = swap (π a) b \dot_(aso) π \dot_(aso) x.
Proof. by rewrite -!actM tfinperm_conj_imL. Qed.

Lemma act_conj_imR π a b x : 
  π \dot_(aso) (swap (π^-1 a) b) \dot_(aso) x = swap a (π b) \dot_(aso) π \dot_(aso) x.
Proof. by rewrite -!actM tfinperm_conj_imR. Qed.

Lemma pfixeU π B C : pfixe π (B `|` C) -> pfixe π B /\ pfixe π C. 
Proof.
move=> fixeBC; split; rewrite/pfixe => a Ha.
all: by apply/fixeBC; rewrite in_fsetU Ha ?orbT.
Qed.

Lemma pfixe1 π a : pfixe π [fset a] -> π a = a.
Proof. apply; exact/fset11. Qed.

Lemma pfixe1U π a B : pfixe π (a |` B) -> π a = a /\ pfixe π B.
Proof.
move => fixeaB; split => [|b Hb] ; first exact/fixeaB/fset1U1.
exact/fixeaB/fset1Ur.
Qed.

End BasicNominalTheory.

Section NominalTrivial.

Variables (A : keyType) (asort : finType) (X : choiceType).

Definition trivialact (aso : asort) (π : {finperm A}) (x : X) := x.

Lemma trivialact1 : forall aso x, trivialact aso 1 x = x.
Proof. by []. Qed.

Lemma trivialactM aso π π' x : 
  trivialact aso (π * π') x = trivialact aso π (trivialact aso π' x).
Proof. by []. Qed.

Lemma trivialactproper aso x y π : x = y -> (trivialact aso π x) = (trivialact aso π y).
Proof.  by move ->. Qed.

Definition trivial_nominal_setoid_mixin :=
  @PermSetoidMixin A asort X (@eq X) trivialact trivialact1 trivialactM trivialactproper.

Lemma trivialact_id aso (π : {finperm A})  x :
  (forall a, a \in fset0 -> π a = a) -> trivialact aso π x = x.
Proof. by []. Qed.

Definition trivial_nominal_mixin :=
  @NominalMixin A asort X trivial_nominal_setoid_mixin _ trivialact_id.

Definition trivial_nominal_type :=
  NominalType A asort X trivial_nominal_mixin.

Lemma trivialactE aso π x : trivialact aso π x = x.
Proof. by []. Qed.

End NominalTrivial.

Canonical bool_nominalType (A : keyType) (asort : finType) :=
  NominalType A asort bool (@trivial_nominal_mixin A asort [choiceType of bool]).

Section NominalOpt.

Variables (A : keyType) (asort : finType) (X : @nominalType _ asort (Phant A)).

Definition optact aso (π : {finperm A}) (x : option X) := omap (act aso π) x.

Lemma optact1 aso x : optact aso 1 x = x.
Proof. by case: x => //= a; rewrite act1. Qed.

Lemma optactM aso π π' x : optact aso (π * π') x = optact aso π (optact aso π' x).
Proof. by case: x => //= a; rewrite actM. Qed.

Lemma optactproper aso x y π : x = y -> (optact aso π x) = (optact aso π y).
Proof. by move ->. Qed.

Lemma optactE aso π x : optact aso π (Some x) = Some (π \dot_(aso) x).
Proof. by []. Qed.

Definition opt_nominal_setoid_mixin :=
  @PermSetoidMixin A asort (option X) (@eq _) optact optact1 optactM optactproper.

Definition opt_support aso (o : option X) :=
  if o is Some a then support aso a else fset0.

Lemma optact_id aso (π : {finperm A}) x :
  pfixe π (opt_support aso x) -> optact aso π x = x.
Proof. by case: x => //= a act_pi; rewrite act_id. Qed.

Canonical opt_nominal_mixin :=
  @NominalMixin A asort (option X) opt_nominal_setoid_mixin _ optact_id.

Canonical opt_nominal_type := NominalType A asort (option X) opt_nominal_mixin.

End NominalOpt.

Section NominalList.

Variables (A : keyType) (asort : finType) (X : @nominalType _ asort (Phant A)).

Definition listact aso π (l : seq X) := map (act aso π) l.

Lemma listact1 aso l : listact aso 1 l = l.
Proof.
elim: l => //= a l IHl. by rewrite act1 IHl.
Qed.

Lemma listactM aso π π' l : listact aso (π * π') l = listact aso π (listact aso π' l).
Proof.
elim: l => //= a l IHl. by rewrite actM IHl.
Qed.

Lemma listactproper aso l1 l2 π : l1 = l2 -> listact aso π l1 = listact aso π l2.
Proof. by move ->. Qed.

Definition list_nominal_setoid_mixin :=
  @PermSetoidMixin A asort (seq X) (@eq (seq X)) listact listact1 listactM listactproper.

Definition list_support aso (l : seq X) := fsetU_list [seq support aso x | x <- l].

Lemma listact_id aso (π : {finperm A}) l :
  pfixe π (list_support aso l) -> listact aso π l = l.
Proof.
elim: l => //= x l IHl Hal.
rewrite IHl => [|a a_supp_l].
  rewrite act_id //= => a a_supp_x.
  apply Hal. by rewrite /list_support/= in_fsetU a_supp_x.
apply Hal. by rewrite /list_support /= in_fsetU a_supp_l orbT.
Qed.

Definition list_nominal_mixin :=
  @NominalMixin A asort _ list_nominal_setoid_mixin _ listact_id.

Canonical list_nominal_type := NominalType A asort (seq X) list_nominal_mixin.

Lemma listactE aso π (l : seq X) : π \dot_(aso) l = [seq π \dot_(aso) x | x <- l].
Proof. by []. Qed.

Lemma cons_support aso (l : seq X) (x : X) :
  list_support aso (x :: l) = (support aso x) `|` (list_support aso l).
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
Variables (A : keyType) (asort : finType) (X Y : @nominalType _ asort (Phant A)).

Implicit Type (x : X * Y).

Definition prodact aso π x := (π \dot_(aso) x.1, π \dot_(aso) x.2).

Lemma prodact1 aso : forall x, prodact aso 1 x = x.
Proof. by case => x y; rewrite /prodact !act1. Qed.

Lemma prodactM aso π π' :
  forall x, prodact aso (π * π') x = prodact aso π (prodact aso π' x).
Proof. by case => x y /=; rewrite /prodact !actM. Qed.

Lemma prodactproper aso : forall x y π, x = y -> (prodact aso π x) = (prodact aso π y).
Proof. by move => x y π ->. Qed.

Definition prod_nominal_setoid_mixin :=
  @PermSetoidMixin A asort (X * Y) (@eq (X * Y)) prodact prodact1 prodactM prodactproper.

Lemma prodact_id aso (π : {finperm A}) x :
     pfixe π (support aso x.1 `|` support aso x.2) -> prodact aso π x = x.
Proof.
case: x => x y Hsupp. rewrite /prodact !act_id //= => a asupp; apply Hsupp;
rewrite in_fsetU asupp ?orbT //.
Qed.

Definition prod_nominal_mixin :=
  @NominalMixin A asort _ prod_nominal_setoid_mixin _ prodact_id.

Canonical prod_nominal_type :=
  NominalType A asort (X * Y) prod_nominal_mixin.

Lemma prodactE aso π (y : X) (z : Y) : π \dot_(aso) (y, z) = (π \dot_(aso) y, π \dot_(aso) z).
Proof. by []. Qed.

End NominalProd.

Section NominalSatoms.

Variable (asort : finType).

Definition satom := (asort * atom)%type.

Implicit Types (π : {finperm atom}).

Definition satomact s π (a : satom) :=
  (a.1, if s == a.1 then π a.2 else a.2).
  
Lemma satomact1 s (a : satom) : satomact s 1 a = a.
Proof. rewrite/satomact finsfun1 if_same. by case: a. Qed.

Lemma satomactM s : 
  forall π π' (a : satom), satomact s (π * π') a = satomact s π (satomact s π' a).
Proof.
rewrite/satomact => π π' [s' a] /=.
case: (s == s') => //. by rewrite finsfunM.
Qed.

Lemma satomactproper s (x y : satom) π : x = y -> (satomact s π x) = (satomact s π y).
Proof. by move ->. Qed.

Definition satom_nominal_setoid_mixin :=
  @PermSetoidMixin _ asort satom (@eq satom) satomact satomact1 satomactM satomactproper.

Definition satom_support s (a : satom) :=
  if s == a.1 then [fset a.2] else fset0.
  
Lemma satomact_id s π a :
     pfixe π (satom_support s a) -> satomact s π a = a.
Proof. 
case: a => [s' a] /=. rewrite /satomact/satom_support/=. 
by case: (s == s') => // /pfixe1 ->.
Qed.

Definition satom_nominal_mixin :=
  @NominalMixin _ asort satom satom_nominal_setoid_mixin _ satomact_id.

Canonical satom_nominal_type := NominalType atom asort satom satom_nominal_mixin.

(* Lemma swapL (a b : satom) : (swap a b) \dot a = b. *)
(* Proof. by rewrite /act /= /satomact tfinpermL. Qed. *)

(* Lemma swapR (a b : satom) : (swap a b) \dot b = a. *)
(* Proof. by rewrite /act /= /satomact tfinpermR. Qed. *)

Lemma satomactE s π (a : satom) :
  π \dot_(s) a = (a.1, if s == a.1  then π a.2 else a.2).
by [].
Qed.

(* Proof. rewrite/act/=/satomact. by case: (s == s'). Qed. *)

End NominalSatoms.

(* Section NominalAtomSubsets. *)

(* Implicit Types (π : {finperm atom}) (A : {fset atom}). *)

(* Definition ssatomact π A := im π A. *)

(* Lemma ssatomact1 : forall A, ssatomact 1 A = A. *)
(* Proof. *)
(* move => A /=; rewrite -{2}[A](im_id A). apply im_eq1 => a. *)
(* by rewrite finsfun1. *)
(* Qed. *)

(* Lemma ssatomactM : forall π π' A, ssatomact (π * π') A = ssatomact π (ssatomact π' A). *)
(* Proof. *)
(* move => π π' A /=; rewrite /ssatomact -imM. apply im_eq1 => a. *)
(* by rewrite finsfunM. *)
(* Qed. *)

(* Lemma ssatomactproper : forall A B π, A = B -> (ssatomact π A) = (ssatomact π B). *)
(* Proof. by move => A B π ->. Qed. *)

(* Lemma ssatomact_id π A : *)
(*   (forall b, b \in A -> π b = b) -> ssatomact π A = A. *)
(* Proof. *)
(* move => Asupp /=; apply/fsetP => a; apply/imfsetP/idP => [[b bA]->|aA]. *)
(*   rewrite Asupp; exact: valP. *)
(* exists (FSetSub aA) => //. by rewrite Asupp. *)
(* Qed. *)

(* (* bricolage *) *)

(* Definition code (A : {fset atom}) := fset_keys A. *)
(* Definition decode (s : seq atom) := seq_fset s. *)

(* Lemma fset_codeK : cancel code decode. *)
(* Proof. *)
(* Admitted. *)


(* Definition finSet_ChoiceMixin := CanChoiceMixin fset_codeK. *)
(* Canonical finset_choiceType := Eval hnf in ChoiceType {fset atom} finSet_ChoiceMixin. *)

(* Definition ssatom_nominal_setoid_mixin := *)
(*   @PermSetoidMixin _ {fset atom} (@eq {fset atom}) ssatomact ssatomact1 ssatomactM ssatomactproper. *)

(* Definition ssatom_nominal_mixin := *)
(*   @NominalMixin _ {fset atom} ssatom_nominal_setoid_mixin _ ssatomact_id. *)

(* Canonical ssatom_nominal_type := *)
(*   @NominalType atom {fset atom} ssatom_nominal_mixin. *)

(* Lemma mem_imperm π A (a : atom) : (π a \in π \dot A) = (a \in A). *)
(* Proof. by apply/mem_im/finperm_inj. Qed. *)

(* End NominalAtomSubsets. *)

Section Freshness.

Context (asort : finType).
Implicit Types (X Y : @nominalType _ asort (Phant atom)).  

Definition max (A : {fset atom}) := \max_(a : A) val a.

Definition fresh_in s {X} (x : X) : atom := (max (support s x)).+1.

Definition supports X s (A : {fset atom}) (x : X) :=
  forall (π : {finperm atom}), (forall a : atom, a \in A -> π a = a) -> π \dot_(s) x = x.

Lemma supportsP {X} s (x : X) :
  supports s (support s x) x.
Proof.
move => π.
exact: act_id.
Qed.

(* Lemma in_le_max x (A : {fset atom}) : x \in A -> x <= max A. *)
(* Proof. *)
(* Admitted. *)

(* Lemma fresh_notin (s : asort) (A : {fset atom}) : (fresh_in s A) \notin A. *)
(* Proof. *)
(*   rewrite /fresh_in /support /=. *)
(*   have bounded: forall x, x \in A -> x != (max A).+1. *)
(*   move=> x xinA. rewrite neq_ltn. apply/orP. *)
(*   apply: or_introl. by apply: in_le_max. *)
(*   apply/memPn; apply: bounded. *)
(* Qed. *)

(* Lemma fresh_neq_in (A : {fset atom}) a : a \in A -> a != fresh_in A. *)
(* Proof. apply contraL => /eqP ->. exact: fresh_notin. Qed. *)

(* Lemma fresh_neq (x : atom) : x != fresh_in x. *)
(* Proof. rewrite/fresh_in/support/=. *)
(* Admitted. *)

(* Lemma supports_fsetP (A B  : {fset atom}) : reflect (supports A B) (B `<=` A). *)
(* Proof. *)
(* apply: (iffP idP) =>[/fsubsetP B_sub_A π fix_A|A_supp_B]. *)
(*   apply ssatomact_id => b /B_sub_A. exact: (fix_A b). *)
(* apply/fsubsetP => a aB. *)
(* apply contraT => aNA. *)
(* have a_fAB : swap a (fresh_in (A, B)) \dot B = B. *)
(* apply A_supp_B => b bA. apply/tfinpermNone/andP. split. *)
(*   apply/eqP => H; subst; by rewrite bA in aNA. *)
(*   have : b \in A `|` B by rewrite in_fsetU bA. *)
(*     exact: fresh_neq_in. *)
(* have : fresh_in (A, B) \in A `|` B. *)
(*   rewrite in_fsetU; apply /orP; right. *)
(*   by rewrite -(tfinpermL a (fresh_in (A, B))) -{2}a_fAB ?mem_imperm. *)
(* by move/fresh_neq_in/eqP. *)
(* Qed. *)

(* Lemma supportsI (X : {nominalType atom}) (A B : {fset atom}) (x : X) : *)
(*   supports A x -> supports B x -> supports (A `&` B) x. *)
(* Proof. *)
(* (* suppose le théorème de décomposition des permutations en *)
(*    produit de transpositions *) *)
(* Admitted. *)


(* Definition fresh X a (x : X) := exists (S : {fset atom}), a \notin S /\ supports S x. *)

(* Notation "a # x" := (fresh a x) (x at level 60, at level 60). *)

(* Lemma fresh1P X (x : X) : (fresh_in x) # x. *)
(* Proof. *)
(* exists (support x). *)
(* split. *)
(*   exact: fresh_notin. *)
(* exact: supportsP. *)
(* Qed. *)

(* Lemma fresh_equiv (X : {nominalType atom}) (x : X) a (π : {finperm atom}) : *)
(*   (a # x) <-> (π a) # (π \dot x). *)
(* Proof. *)
(* wlog suff : x π a / a # x -> (π a) # (π \dot x) => Hsuff. *)
(*   split; first by apply Hsuff. *)
(*   rewrite -{2}[a](finpermK π) -{2}[x](actK π). *)
(*   exact: Hsuff. *)
(* move : Hsuff => [S] [aNS supp_S_x]. *)
(* exists (π \dot S). split; first by rewrite mem_imperm. *)
(* move => Ɣ HƔ. apply (@act_inj _ _ π^-1). rewrite actK -2?actM. *)
(* apply supp_S_x => b bS. rewrite finsfunM /= finsfunM /= HƔ; *)
(*   first exact: finpermK. *)
(* by rewrite mem_imperm. *)
(* Qed. *)

(* Lemma im_fresh (X : {nominalType atom}) (π : {finperm atom}) a (x : X) : *)
(*   a # (π^-1 \dot x) -> (π a) # x. *)
(* Proof. by rewrite -{2}[x](actVK π); apply fresh_equiv. Qed. *)

(* Lemma im_inv_fresh (X : {nominalType atom}) (π : {finperm atom}) a (x : X) : *)
(*   a # (π \dot x) -> (π^-1 a) # x. *)
(* Proof. rewrite -{2}[x](actK π). by apply fresh_equiv. Qed. *)

(* Lemma CFN_principle b {X : {nominalType atom}} {a} {x : X} : *)
(*   b # x -> swap a b \dot x = x -> a # x. *)
(* Proof. *)
(* move => bFx abx_eq_x. *)
(* apply (@fresh_equiv _ _ _ (swap a b)). *)
(* by rewrite tfinpermL abx_eq_x. *)
(* Qed. *)

(* Lemma fresh_atomP (x y : atom) : reflect (x # y) (x != y). *)
(* Proof. *)
(* apply: (iffP idP) => [xNy| [S] [xNS S_supp_y]]. *)
(*   apply (@CFN_principle (fresh_in y)); first exact: fresh1P. *)
(*   apply/tfinpermNone/andP; split; first by rewrite eq_sym. *)
(*   exact: fresh_neq. *)
(* apply/negP => /eqP x_eq_y. *)
(* rewrite -x_eq_y in S_supp_y. *)
(* have : forall a, a \notin S -> a = x. *)
(*   move => a aNS. rewrite -(tfinpermR a x). apply S_supp_y => b bS. *)
(*   apply/tfinpermNone/andP; split; apply/eqP => H; subst. *)
(*     by rewrite bS in aNS. *)
(*   by rewrite bS in xNS. *)
(* have freshxSNS : (fresh_in (x |` S)) \notin S. *)
(*   move: (fresh_notin (support x `|` S)). *)
(*   by rewrite in_fset1U negb_or => /andP; case. *)
(* move/(_ (fresh_in (x |` S))) /(_ freshxSNS). *)
(* move: (fresh_neq_in (fset1U1 x S)). *)
(* by rewrite eq_sym => /eqP. *)
(* Qed. *)

(* Lemma fresh_atomC (x y : atom) : x # y <-> y # x. *)
(* Proof. *)
(* split => hFresh . *)
(* all: apply/fresh_atomP. *)
(* all: rewrite eq_sym. *)
(* all: by apply/fresh_atomP. *)
(* Qed. *)

(* Lemma fresh_fsetP (A : {fset atom}) x : reflect (x # A) (x \notin A). *)
(* Proof. *)
(* apply: (iffP idP) => [xNA|[S] [xNS /supports_fsetP /fsubsetP S_supp_A ]]. *)
(*   exists A. split => //. exact: supportsP. *)
(* exact: (contra (S_supp_A x)). *)
(* Qed. *)

(* Lemma fresh_fsetU1 (A B : {fset atom}) x : x # (A `|` B) -> x # A. *)
(* Proof. *)
(* move/fresh_fsetP. *)
(* rewrite in_fsetU negb_or => /andP [? _]. *)
(* exact/fresh_fsetP. *)
(* Qed. *)

(* Lemma fresh_fsetU2 (A B : {fset atom}) x : x # (A `|` B) -> x # B. *)
(* Proof. *)
(* move/fresh_fsetP. *)
(* rewrite in_fsetU negb_or => /andP [_ ?]. *)
(* exact/fresh_fsetP. *)
(* Qed. *)

(* Lemma fresh_support X a (x : X) : a \notin (support x) -> a # x. *)
(* Proof. *)
(* move => aNx. exists (support x). *)
(* split => //. *)
(* exact: supportsP. *)
(* Qed. *)

(* Lemma act_fresh {X : {nominalType atom}} (a b : atom) (x : X) : *)
(*       a # x -> b # x -> swap a b \dot x = x. *)
(* Proof. *)
(* move => [Sa [aNSa supp_Sa_x]] [Sb [bNSb supp_Sb_x]]. *)
(* have supp_SaISb_x : supports (Sa `&` Sb) x by apply: supportsI. *)
(* apply supp_SaISb_x => c. rewrite in_fsetI => /andP [cSa cSb]. *)
(* have aNc : c != a. *)
(*   apply/negP => /eqP a_eq_c. move: cSa aNSa. *)
(*   by rewrite a_eq_c => ->. *)
(* have bNc : c != b. *)
(*   apply/negP => /eqP b_eq_c. move: cSb bNSb. *)
(*   by rewrite b_eq_c => ->. *)
(* apply tfinpermNone. *)
(* by rewrite aNc bNc. *)
(* Qed. *)

(* Lemma fresh_prod X Y a (x : X) (y : Y) : a # (x, y) <-> (a # x) /\ (a # y). *)
(* Proof. *)
(* split. *)
(*   move => [S] [aNS supp_S_xy]. *)
(*   split; exists S; split => //; move => π /(supp_S_xy π); rewrite prodactE. *)
(*     by move/(congr1 fst). *)
(*   by move/(congr1 snd). *)
(* move => [[Sx] [aNSx supp_Sx_x] [Sy] [aNSy supp_Sy_y]]. *)
(* exists (Sx `|` Sy); split. *)
(*   by rewrite in_fsetU negb_or aNSx aNSy. *)
(* move => π H. rewrite prodactE. *)
(* have -> : π \dot x = x. *)
(*   apply (supp_Sx_x π) => b bSx. apply H. *)
(*   by rewrite in_fsetU bSx. *)
(* suff : π \dot y = y by move ->. *)
(* apply (supp_Sy_y π) => b bSy. apply H. *)
(*   by rewrite in_fsetU bSy orbT. *)
(* Qed. *)

(* Lemma fresh_nil {X} a : a # @nil X. *)
(* Proof. *)
(* exists fset0. split => //. *)
(* by rewrite in_fset0. *)
(* Qed. *)

(* Lemma supports_cons {X} S (x : X) (l : seq X): *)
(*   supports S (x :: l) -> supports S x /\ supports S l. *)
(* Proof. *)
(* move => S_supp_xl. *)
(* split => π HS. *)
(* all: move : (S_supp_xl π HS) => /= /eqP. *)
(* all: by rewrite !listactE /= eqseq_cons => /andP [/eqP ? /eqP ?]. *)
(* Qed. *)

(* Lemma fresh_cons {X} (l : seq X) a x : a # (x :: l) <-> a # x /\ a # l. *)
(* Proof. *)
(* split. *)
(*   move => [S] [aNS /supports_cons [S_supp_x S_supp_l]]. *)
(*   split; by exists S; split => //. *)
(* move => [[Sa] [aNSa Sa_supp_x] [Sl] [aNSl Sl_supp_l]]. *)
(* exists (Sa `|` Sl); split. *)
(*   by rewrite in_fsetU negb_or aNSa aNSl. *)
(* move => π H. *)
(* Admitted. *)

(* Lemma fresh_list {X} (l : seq X) a : a # l <-> forall x, x \in l -> a # x. *)
(* Proof. *)
(* elim: l => [|b l IH]. *)
(*   split => // ?; exact/fresh_nil. *)
(* split => [/fresh_cons [aFb aFl] y|Hbl]. *)
(*    rewrite inE => /orP. case. *)
(*     by move /eqP ->. *)
(*   exact/(iffLR IH aFl). *)
(* apply fresh_cons; split. *)
(*   exact/Hbl/mem_head. *)
(* apply IH => x xl; apply/Hbl. *)
(* by rewrite in_cons xl orbT. *)
(* Qed. *)

(* Lemma fresh_map {T : finType} {X : {nominalType atom}} (f : T -> X) a : *)
(*   a # [seq f i | i : T] -> forall i, a # f i. *)
(* Proof. *)
(* move/fresh_list => H i. *)
(* exact/H/map_f/mem_enum. *)
(* Qed. *)

(* Lemma fresh_fun {I : finType} {X} (f : I -> X) a i : *)
(*   a # f -> a # f i. *)
(* Proof. *)
(* move => [S] [aNS S_supp_f]. *)
(* exists S; split => // π H. *)
(* have πf_eq_f : π \dot f = f by apply/S_supp_f. *)
(* by rewrite -ffunactE πf_eq_f. *)
(* Qed. *)

(* Lemma fresh_perm (X : {nominalType atom}) (π : {finperm atom}) (x : X) : *)
(*   [disjoint (support x) & finsupp π] -> π \dot x = x. *)
(* Proof. *)
(* move => /fdisjointP disj_x_π. *)
(* apply act_id => a /disj_x_π. *)
(* exact: finsfun_dflt. *)
(* Qed. *)

(* Lemma tfinperm_fresh (a b c : atom) : a # c -> b # c -> swap a b c = c. *)
(* Proof. *)
(* move => aFc bFc. *)
(* apply/tfinpermNone/andP; split. *)
(* all: exact/fresh_atomP/fresh_atomC. *)
(* Qed. *)

(* Lemma disjoint_tfsupp a b S : *)
(*   a # S -> b # S -> [disjoint finsupp (swap a b) & S]. *)
(* Proof. *)
(* move => aFS bFS. rewrite fdisjoint_sym. *)
(* by apply/tfinperm_disj; exact/fresh_fsetP. *)
(* Qed. *)

(* Lemma disjoint_conj (π π' : {finperm atom}) T : *)
(*   [disjoint finsupp π & T] -> [disjoint finsupp π' & T] -> *)
(*   [disjoint finsupp (π * π') & T]. *)
(* Proof. *)
(* move => /fdisjointP disj_pi_T /fdisjointP disj_pi'_T. *)
(* apply/fdisjointP => a /(fsubsetP (finsupp_conj π' π) a). *)
(* by rewrite in_fsetU => /orP [?|?]; auto. *)
(* Qed. *)

(* Lemma disj_im_fresh (π : {finperm atom}) T x : *)
(*   [disjoint finsupp π & T] -> x # T -> π x # T. *)
(* Proof. *)
(* move => /fdisjointP disj_pi_T xFT. *)
(* have [/eqP ->|pix_neq_x] := boolP (π x == x) => //. *)
(* have : π (π x) != π x. *)
(*   apply/negP => /eqP/finperm_inj. *)
(*   by move: pix_neq_x => /eqP. *)
(* by rewrite -mem_finsupp => /disj_pi_T /fresh_fsetP. *)
(* Qed. *)

End Freshness.

(* Notation "a # x" := (fresh a x) (x at level 60, at level 60). *)

(* Ltac freshTac := *)
(*   match goal with *)
(*     | |- (fresh_in ?x) # ?x => apply fresh1P *)
(*     | |- ?a # ?x => *)
(*       try (subst a); *)
(*       match goal with *)
(*         | |- fresh_in ?y  # ?x => move : (fresh1P y) *)
(*       end; *)
(*       do ?[case/fresh_prod|move=> ?] *)
(*   end. *)


(* Ltac freshTacCtxt z := *)
(*   match goal with *)
(*       | [ y := fresh_in ?x |- _] => match y with *)
(*         | z => move: (fresh1P x); rewrite -/z *)
(*                                     end *)
(*       | _ => fail "not a fresh variable" *)
(*   end; *)
(*   do ?[case/fresh_prod|move=> ?]. *)

(* Ltac freshTacList := *)
(*   match goal with *)
(*   | |- ?z # ?t  => *)
(*     match goal with *)
(*       | [ H : is_true (t \in ?l) |- _] => apply (@fresh_list _ l) => // *)
(*     end *)
(* end. *)


(* (* fresh_dec (e : list { X : nominalType & X }) nom : is_fresh_dec x y -> is_fresh (fresh_in (interp e x)) (interp e y) *) *)
(* (* Hint Extern 0 (@is_fresh _ _ _) => eapply fresh_in_fresh : typeclass_instances. *) *)
(* (*Hint Mode is_fresh + - - : typeclass_instances.*) *)

(* Section EquivariantFunctions. *)

(* Implicit Types (W X Y Z: {nominalType atom}) (π : {finperm atom}). *)

(* Definition equivariant1 X Y (f : X -> Y) := forall π x, f (π \dot x) = π \dot (f x). *)

(* Definition equivariant2 X Y Z (f : X -> Y -> Z) := *)
(*   forall π x y,  f (π \dot x) (π \dot y) = π \dot (f x y). *)

(* Definition equivariant3 X Y Z W (f :  X -> Y -> Z -> W) := *)
(*   forall π x y z, f (π \dot x) (π \dot y) (π \dot z) = π \dot (f x y z). *)

(* Definition equivariant_prop X Y (R : X -> Y -> Prop) := *)
(*   forall π x y, R (π \dot x) (π \dot y) <-> R x y. *)

(* Lemma all2_equivariant {A : {nominalType atom}} (s1 s2 : seq A) (p : A -> A -> bool) π : *)
(*   equivariant2 p -> *)
(*   all2 p (π \dot s1) (π \dot s2) = all2 p s1 s2. *)
(* Proof. *)
(* move => p_equi. *)
(* rewrite all2_map. apply all2_eq => x y. *)
(* exact/p_equi. *)
(* Qed. *)

(* Lemma map_equivariant {A B : {nominalType atom}} (f : A -> B) l π : *)
(*   (forall x, x \in l -> π \dot f x = f (π \dot x)) -> *)
(*    π \dot (map f l) = map f (π \dot l). *)
(* Proof. *)
(* move => f_equiv. *)
(* rewrite listactE -!map_comp. *)
(* apply/eq_in_map => t tl /=. *)
(* exact/f_equiv. *)
(* Qed. *)

(* Lemma if_equivariant {X : {nominalType atom}} (u v : X) b π : *)
(*   π \dot (if b then u else v) = if b then (π \dot u) else π \dot v. *)
(* Proof. by case: b. Qed. *)

(* Lemma equi_funprop X Y Z (f : X -> Y -> Z) (R : Z -> Z -> Prop) : *)
(*   equivariant2 f -> equivariant_prop R -> *)
(*   equivariant_prop (fun (x : X) (y : Y * Y) => R (f x y.1) (f x y.2)). *)
(* Proof. *)
(* move => equi_f equi_R π x; case => y y' /=. *)
(* by rewrite !equi_f equi_R. *)
(* Qed. *)

(* Lemma swap_equiv X : *)
(*   equivariant2 (fun (a : atom) (z : atom * X) => swap z.1 a \dot z.2). *)
(* Proof. *)
(* move => π a; case => b x /=. by rewrite -!actM tfinperm_conj. *)
(* Qed. *)

(* End EquivariantFunctions. *)

(* (* Section FinitelySupportedFunctions. *) *)

(* (* Implicit Types (V W X Y Z : nominalType atom) (π : {finperm atom}) (S : {fset atom}). *) *)

(* (* Definition fsupports1 {X Y} (f : X -> Y) S := *) *)
(* (*   forall a b x, (swap a b) \dot (f x) = f (swap a b \dot x). *) *)

(* (* Definition finitely_supported1 X Y (f : X -> Y) := *) *)
(* (*   exists S, fsupports1 f S. *) *)

(* (* Definition fsupports2 X Y Z (f : X -> Y -> Z) S := *) *)
(* (*    forall a b x y, swap a b \dot (f x y) = *) *)
(* (*                    f (swap a b \dot x) (swap a b \dot y). *) *)

(* (* Definition finitely_supported2 X Y Z (f : X -> Y -> Z) := *) *)
(* (*   exists S, fsupports2 f S. *) *)

(* (* Definition fsupports *) *)

(* (* Definition function_support *) *)

(* (* End FinitelySupportedFunctions. *) *)

(* (* Section StrongSupport. *) *)

(* (* Variables (X : nominalType) (S : {fset atom}). *) *)
(* (* Implicit Types (x : X). *) *)

(* (* (* (* hypothèse qui implique que S est le plus petit support de x *) *) *) *)
(* (* (* Hypothesis strong_support :  *) *) *)
(* (* (*   forall x π, π \dot x = x -> (forall a : atom, a \in (support x) -> π a == a). *) *) *)

(* (* (* Lemma equi_support : equivariant1 (@support X). *) *) *)
(* (* (* Proof. *) *) *)
(* (* (* move => π x. *) *) *)
(* (* (* wlog suff : x π / im π (support x) `<=` support (π \dot x). *) *) *)
(* (* (*   move => Hsuff; apply/eqP; rewrite eqEfsubset; apply/andP; split; last by apply Hsuff. *) *) *)
(* (* (*   rewrite -(actVK π (support (π \dot x))) -{2}[x](actK π x); *) *) *)
(* (* (*   exact/im_subset/Hsuff. *) *) *)
(* (* (* apply/fsubsetP => a /imfsetP [b bx] ->. apply contraT => πbNπx. *) *) *)
(* (* (* set c := fresh_in (val b, im π^-1 (support (π \dot x))). *) *) *)
(* (* (* have : swap (val b) c \dot x = x. *) *) *)
(* (* (*   apply (@act_inj _ π). rewrite -actM tfinperm_conj actM act_fresh //. *) *) *)
(* (* (*     exact: fresh_support πbNπx. *) *) *)
(* (* (*   exists (support (π \dot x)). *) *) *)
(* (* (*   split; last exact: supportsP. *) *) *)
(* (* (*   rewrite -(actVK π (support (π \dot x))) mem_im. *) *) *)
(* (* (*     by admit.   *) *) *)
(* (* (*   exact: finperm_inj. *) *) *)
(* (* (* have {bx} bx : val b \in support x. by apply valP. *) *) *)
(* (* (* move/strong_support => H. move: (H (val b) bx). *) *) *)
(* (* (* rewrite tfinpermL => /eqP cvalb.  *) *) *)
(* (* (* Admitted. *) *) *)


(* (* End StrongSupport. *) *)

(* Section SomeAny. *)

(* Implicit Type (X : {nominalType atom}). *)

(* Definition new (P : atom -> Prop) := *)
(*   exists A : {fset atom}, forall a, a # A -> P a. *)

(* Notation "\new a , P" := (new (fun a : nat => P)) *)
(*    (format "\new  a ,  P", at level 10). *)
(* Notation "a # x" := (fresh a x) (x at level 60, at level 60). *)

(* Theorem some_any X (R : atom -> X -> Prop) : *)
(*   equivariant_prop R -> *)
(*   forall x : X, [/\ *)
(*       (forall a : atom , a # x -> R a x) -> (\new a, (R a x)), *)
(*       (\new a, (R a x)) ->  R (fresh_in (support x)) x, *)
(*       R (fresh_in (support x)) x -> (exists2 a, a # x & R a x) & *)
(*       (exists2 a, a # x & R a x) *)
(*       -> (forall a, a # x -> R a x) *)
(*     ]. *)
(* Proof. *)
(* move => Requi; split. *)
(*   - exists (support x) => a /fresh_fsetP/fresh_support. exact: (H a). *)
(*   - move => [S aNSR]. *)
(*     apply/(Requi (swap (fresh_in x) (fresh_in (x,S)))). *)
(*     rewrite swapL [_ \dot x]act_fresh; try (by freshTac). *)
(*     apply/aNSR. by freshTac. *)
(*   - move => Rfresh. exists (fresh_in x) => //. exact: fresh1P. *)
(*   - move => [a a_fresh_x rax] a' a'_fresh_x. *)
(*     rewrite -[a'](tfinpermL a a') -[x](@act_fresh _ a a') //. *)
(*     by apply/Requi. *)
(* Qed. *)

(* Lemma new_forall X (R : atom -> X -> Prop) : *)
(*   equivariant_prop R -> *)
(*   forall x : X, ((\new a, (R a x)) <-> (forall a, a # x -> R a x)). *)
(* Proof. *)
(* move=> Requi x. have [? ne ef] := some_any Requi x. *)
(* by split => // /ne /ef. *)
(* Qed. *)

(* Lemma new_exists X (R : atom -> X -> Prop) : *)
(*   equivariant_prop R -> *)
(*   forall x : X, ((\new a, (R a x)) <-> (exists2 a, a # x & R a x)). *)
(* Proof. *)
(* move=> Requi x; have [fn nf nh ef] := some_any Requi x. *)
(* by split => [/nf/nh|/ef]. *)
(* Qed. *)

(* Lemma fresh_new X (R : atom -> X -> Prop) : *)
(*   equivariant_prop R -> *)
(*   forall x: X, R (fresh_in x) x <-> \new a, (R a x). *)
(* Proof. *)
(* move=> Requi x. have [fn nf nh ef] := some_any Requi x. *)
(* by split => [/nh/ef/fn | /nf]. *)
(* Qed. *)

(* Lemma some_fresh_new X (R : atom -> X -> Prop) : *)
(*   equivariant_prop R -> *)
(*   forall (y : atom) (x : X), y # x -> (R y x) <-> \new a, (R a x). *)
(* Proof. *)
(* move => Requi y x yFx. *)
(* split => [Ryx|/(new_forall Requi) new_Rax]. *)
(*   apply new_exists => //. *)
(*   by exists y. *)
(* exact/new_Rax. *)
(* Qed. *)

(* Lemma new_eq P1 P2 : *)
(*  (forall z, P1 z <-> P2 z) -> (\new z, (P1 z)) <-> (\new z, (P2 z)). *)
(* Proof. *)
(* move => P1_eq_P2. *)
(* split. *)
(* all: move => [S] HS; exists S => a aFS. *)
(* all: exact/P1_eq_P2/(HS _ aFS). *)
(* Qed. *)

(* Lemma new_all {Y : finType} (P : Y -> atom -> Prop) : *)
(*   \new z, (forall y, P y z) <-> forall y, \new z, (P y z). *)
(* Proof. *)
(* split. *)
(*   move => [S] HS y. *)
(*   exists S => a aFS. *)
(*   exact/HS. *)
(* move/fin_all_exists => [Supp] HSupp. *)
(* exists (\fbigcup_(y in Y) (Supp y)) => a aFSuppy y. *)
(* apply HSupp. *)
(* Admitted. *)

(* Lemma new_and P1 P2 : *)
(*   \new z, (P1 z /\ P2 z) <-> (\new z, (P1 z) /\ \new z, (P2 z)). *)
(* Proof. *)
(* split. *)
(*   move => [S] HS; split; *)
(*   exists S => a aFS. *)
(*     exact: (proj1 (HS _ aFS)). *)
(*   exact: (proj2 (HS _ aFS)). *)
(* move => [[S1] HS1 [S2] HS2]. *)
(* exists (S1 `|` S2) => a aFS1S2; split. *)
(*   exact/(HS1 a)/(fresh_fsetU1 aFS1S2). *)
(* exact/(HS2 a)/(fresh_fsetU2 aFS1S2). *)
(* Qed. *)

(* Lemma new_andb P1 P2 : *)
(*   \new z, (P1 z && P2 z) <-> (\new z, (P1 z) /\ \new z, (P2 z)). *)
(* Proof. *)
(* have andb_eq_and : \new z, (P1 z && P2 z) <-> \new z, (P1 z /\ P2 z). *)
(*   apply new_eq; split => [/andP|? ] //; exact/andP. *)
(* split. *)
(*   move/andb_eq_and. by apply new_and. *)
(* move => ?. exact/andb_eq_and/new_and. *)
(* Qed. *)


(* Lemma new_all2 {A : eqType} {p : atom -> A -> A -> bool} {l1 l2 : seq A} : *)
(*   (\new z, (all2 (p z) l1 l2)) <-> (all2_prop (fun t1 t2 => \new z, (p z t1 t2)) l1 l2). *)
(* Proof. *)
(* elim: l1 l2 => /=. *)
(*   move => [|a l2]; split => //. *)
(*     by move => _; exists fset0 => //. *)
(*   by move => [S] /(_ _ (fresh1P S)). *)
(* move => a1 l1 IHl1 [|a2 l2]. *)
(*   split => //. by move => [S] /(_ _ (fresh1P S)). *)
(* split. *)
(*   move/new_andb => [? ?]; split => //. *)
(*   by apply/IHl1. *)
(* move => [? ?]; apply/new_andb; split => //. *)
(* by apply/IHl1. *)
(* Qed. *)


(* End SomeAny. *)

(* Notation "\new a , P" := (new (fun a : nat => P)) *)
(*    (format "\new  a ,  P", at level 10). *)
(* Notation "a # x" := (fresh a x) (x at level 60, at level 60). *)
