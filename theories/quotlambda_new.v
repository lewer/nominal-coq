Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq.
Require Import bigop fintype finfun finset generic_quotient perm.
Require Import tuple.
Require Import fingroup.
Require Import finmap.
Require Import finsfun.
Require Import Program.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope finperm_scope with fperm.
Local Open Scope finperm_scope.
Local Open Scope fset.
Local Open Scope quotient_scope.

Definition atom := nat.

Section FinPermDef.

Record finPerm := FinPerm {
  perm_of :> finsfun (@id atom);
  _ : injectiveb_finsfun_id  perm_of
}.

Lemma finperm_inj (π : finPerm) : injective π.
Proof. by case:π => *; apply/injectiveb_finsfunP. Qed.

Lemma in_permsupp (π : finPerm) : {mono π : a / a \in finsupp π}.
Proof. 
move=> a; case: π => f /=.
move=> /andP [/finsfun_injective_inP f_inj_in /forallP f_stable].
by case: (finsuppP _ a) => [/negPf -> //|af]; apply: (f_stable (SeqSub af)).
Qed.

Lemma perm_stable (π : finPerm) (S : {fset atom}) :
  finsupp π \fsubset S -> forall (a : atom), a \in S -> π a \in S. 
Proof.
move=> /fsubsetP S_surfinsupp a; case:finsuppP; first by []. 
by move => a_supp aS; apply/S_surfinsupp/(monoW (@in_permsupp _)).
Qed.

Definition eq_finPerm (π π' : finPerm) :=
    [forall a: (finsupp π :|: finsupp π'), π (val a) == π' (val a) :> nat].

Lemma eq1_finPermP (π π' : finPerm) : reflect (π =1 π') (eq_finPerm π π').
Proof.
apply: (iffP idP); last first.
  move => π_eq_π'. apply/forallP => *. by apply/eqP/π_eq_π'.
move => /forallP π_eq_π' a. 
have [aππ'|aNππ'] := boolP (a \in (finsupp π :|: finsupp π')).
  by apply/eqP/(π_eq_π' (SeqSub aππ')).
move:aNππ'; rewrite in_fsetU negb_or => /andP [aNπ aNπ'].
by rewrite !finsfun_dflt.
Qed.

Lemma eq_finPermP (π π' : finPerm) : π =1 π' <-> π = π'.
Proof.
split; last by move ->.
case: π; case: π' => f f_inj g g_inj g_eq1_f.
suff g_eq_f : g = f.
  move: g_eq_f f_inj g_inj g_eq1_f-> => f_inj g_inj _. congr FinPerm. 
  exact: bool_irrelevance.
by apply/finsfunP.
Qed.

Lemma eq_finPerm_is_equiv : equiv_class_of eq_finPerm.
Proof.
split=> [p|p q|q p r].
  rewrite /eq_finPerm. by apply/forallP.
  rewrite /eq_finPerm. apply/forallP/forallP => H; rewrite fsetUC => x; by rewrite eq_sym. 
move=> /eq1_finPermP pq /eq1_finPermP qr.
by apply/eq1_finPermP => n; rewrite pq qr.
Qed.


End FinPermDef.

Section PermFinPerm.

Definition ffun_of_finPerm (π : finPerm) (S : {fset atom}) 
           (supp_incl_S : finsupp π \fsubset S) := 
  [ffun x:S => SeqSub (perm_stable supp_incl_S (ssvalP x))].

Fact perm_of_finPerm_subproof (π : finPerm) (S : {fset atom}) 
      (supp_incl_S : finsupp π \fsubset S) : injectiveb (ffun_of_finPerm supp_incl_S). 
Proof.
apply/injectiveP => a b; rewrite !ffunE; move/(congr1 val) => πa_eq_πb. 
by apply/val_inj/(finperm_inj πa_eq_πb).
Qed.

Definition perm_of_finPerm (π : finPerm) (S : {fset atom}) 
           (supp_incl_S : finsupp π \fsubset S) := 
  Perm (perm_of_finPerm_subproof supp_incl_S).

Definition can_perm_of_finPerm (π : finPerm) := 
  perm_of_finPerm (fsubsetAA (finsupp π)).

Lemma perm_of_finPermE (π : finPerm) (S : {fset atom}) 
      (supp_incl_S : finsupp π \fsubset S) :
  forall a : S, perm_of_finPerm supp_incl_S a = SeqSub (perm_stable supp_incl_S (ssvalP a)).
Proof. move => a. by rewrite/perm_of_finPerm -pvalE /ffun_of_finPerm /= ffunE. Qed.

(* Probablement inutile 
Let finsfun_of_perm (S : {fset atom}) (p : {perm S}) :=
finsfun_of_fun (@id atom) (fun_of_ffun (@id atom) [ffun x:S => val (p x)]) S. 

Lemma finsfun_of_permE (S : {fset atom}) (p : {perm S}) :
  finsfun_of_perm p =1 fun_of_ffun (@id atom) [ffun x:S => val (p x)].
Proof.
move=> a; rewrite finsfun_of_funE // => {a} a.
by apply: contraNT => /out_fun_of_ffun ->.
Qed.

Lemma finsfun_of_perm_incl (S : {fset atom}) (p : {perm S}) :
  finsupp (finsfun_of_perm p) \fsubset S.
Proof.
apply/fsubsetP => a. 
rewrite mem_finsupp finsfun_of_permE. by apply/contraR/out_fun_of_ffun.
Qed.

Fact finPerm_of_perm_subproof (S : {fset atom}) (p : {perm S}) : 
  injectiveb_finsfun_id (finsfun_of_perm p).
Proof. 
apply/injectiveb_finsfunP/injective_finsfunP; exists S.
  by apply/fsubsetP => a /in_FSetE [].
split.
  move => a b aS bS /=; rewrite !finsfun_of_permE //=. 
  by rewrite !in_fun_of_ffun !ffunE /= => /val_inj /(@perm_inj _ p) [].
  (* :BUG: Why do we need to provide p ? Check with 8.5 *)
by move=> [a aS]; rewrite finsfun_of_permE in_fun_of_ffun ffunE (valP p.[aS])%fmap.
Qed.

Definition finPerm_of_perm (S : {fset atom}) (p : {perm S}) :=
  FinPerm (finPerm_of_perm_subproof p).

Lemma finPerm_of_perm_incl (S : {fset atom}) (p : {perm S}) :
  finsupp (finPerm_of_perm p) \fsubset S.
Proof.
apply/fsubsetP => a. 
rewrite mem_finsupp finsfun_of_permE. by apply/contraR/out_fun_of_ffun.
Qed.

Lemma finPerm_of_permE (S : {fset atom}) (p : {perm S}) (a : atom) (aS : a \in S) :
    (finPerm_of_perm p) a = val (p (SeqSub aS)).
Proof. 
rewrite finsfun_of_funE; first by rewrite in_fun_of_ffun ffunE. 
move => b. apply contraR. exact: out_fun_of_ffun.
Qed.

Lemma support_finPerm_of_permE (S : {fset atom}) (p : {perm S}) :
  (forall a : S, p a != a) -> finsupp (finPerm_of_perm p) = S.
Proof.
move => H. apply/fsetP => a. rewrite mem_finsupp. apply/idP/idP; last first.
  move => aS. rewrite finPerm_of_permE. exact: H.
rewrite -mem_finsupp. exact: fsubsetP (finPerm_of_perm_incl p) a.
Qed.

End PermFinPerm.

*)

End PermFinPerm.

Section FinPermSpec.

Lemma finPerm_can (π : finPerm) (a : atom) (aπ : a\in finsupp π) :
  π a = (val (can_perm_of_finPerm π (SeqSub aπ))).
Proof.
have t : π a = val (SeqSub (perm_stable (fsubsetAA (finsupp π)) aπ)) by []. 
rewrite t. congr val.
by rewrite perm_of_finPermE. 
Qed.

CoInductive finPerm_spec (π : finPerm) (a : atom) : atom -> bool -> Type :=
  | FinPermOut : a \notin finsupp π -> finPerm_spec π a a false
  | FinPermIn  (aπ : a \in finsupp π) : 
      finPerm_spec π a (val (can_perm_of_finPerm π (SeqSub aπ))) true.

Lemma finPermP (π : finPerm) (a : atom) : finPerm_spec π a (π a) (a \in finsupp π).
Proof.
case:finsuppP; first by exact: FinPermOut.
move => aπ. suff: π a = (val (can_perm_of_finPerm π (SeqSub aπ))).
  by move ->; apply: FinPermIn.
exact: finPerm_can.
Qed.

End FinPermSpec.

Section FinPermInvDef.

Variable (π : finPerm).

Let p := can_perm_of_finPerm π.
Let inv_p_ffun := [ffun a : finsupp π => val ( p^-1%g a)].

Fact can_p_subproof : [forall a : finsupp π ,  inv_p_ffun a != val a].
Proof.
apply/forallP => a. rewrite ffunE val_eqE.
rewrite (can2_eq (permKV p) (permK p)).
rewrite perm_of_finPermE -val_eqE eq_sym -mem_finsupp. exact: ssvalP.
Qed.

Definition finsfun_invp_subproof := @finsfun_of_can_ffun _ _ (@id atom) _ _ can_p_subproof.

Fact injective_finsfun_subproof : injectiveb_finsfun_id finsfun_invp_subproof.
Proof.
apply/andP. split; last first.
  apply/forallP => a. rewrite !finsfun_of_can_ffunE; first by apply: valP.
  move => aπ /=. rewrite ffunE. exact: valP.
apply/injectiveP => a b. rewrite !ffunE !finsfun_of_can_ffunE; rewrite ?ssvalP //=.
move => bπ aπ. rewrite !ffunE => pa_eq_pb.
suff: {| ssval := ssval a; ssvalP := aπ |} = {| ssval := ssval b; ssvalP := bπ |}.
  by move/(congr1 val) => /=; apply/val_inj. 
apply/eqP. rewrite -(inj_eq (@perm_inj _ (perm_inv (can_perm_of_finPerm π)))).
rewrite -val_eqE. by apply/eqP.
Qed.

Definition finperm_inv := 
  FinPerm injective_finsfun_subproof.

Lemma finperm_one_subproof : injectiveb_finsfun_id (@finsfun_one nat_KeyType).
Proof. by apply/injectiveb_finsfunP/inj_finsfun_one. Qed.

Definition finperm_one := FinPerm finperm_one_subproof.

End FinPermInvDef. 

Section FinPermMulDef.

Lemma finperm_mul_subproof (π π' : finPerm) :
  injectiveb_finsfun_id (@finsfun_comp nat_KeyType π π').
Proof. apply/injectiveb_finsfunP/inj_finsfun_comp; by apply finperm_inj. Qed.

Definition finperm_mul (π π' : finPerm) :=
  FinPerm (finperm_mul_subproof π π').

End FinPermMulDef.

Notation "1" := finperm_one.
Notation "π * π'" := (finperm_mul π π').
Notation "π ^-1" := (finperm_inv π) : finperm_scope.
Notation "π ~" := (can_perm_of_finPerm π) 
  (at level 0) : finperm_scope.  

Section FinPermTheory.

Implicit Types (π : finPerm) (a : atom).

Lemma can_inv π : π^-1~ = π~^-1%g.
Proof.
apply permP => a. rewrite perm_of_finPermE.
apply val_inj => /=. rewrite finsfun_of_can_ffunE; first by apply: valP.
move => aπ /=. rewrite ffunE.  congr ssval. 
suff : {| ssval := ssval a; ssvalP := aπ |} = a by move ->.
by apply val_inj.
Qed.

Lemma finperm_invK : involutive finperm_inv.
Proof.
move => π. apply/eq_finPermP/eq1_finPermP/forallP. 
rewrite fsetUid => a. rewrite !finPerm_can; do ?apply: valP.
move => aπ ainvinvπ. rewrite val_eqE can_inv can_inv invgK.
suff : ainvinvπ = aπ by move ->.
exact: bool_irrelevance.
Qed.

Lemma myvalK  (S : {fset atom}) (a : S) aS :
  {| ssval := val a;
     ssvalP := aS |} = a.
Proof. by apply val_inj. Qed.

(* le lemme myvalK doit déjà exister, mais je l'ai pas trouvé *)

Lemma finpermK π : cancel π π^-1.
Proof.
move => a. case: (finPermP π a) => [aNπ | aπ].
  by rewrite finsfun_dflt.
rewrite finPerm_can; first by apply: valP.
move => πaπ. by rewrite myvalK can_inv -permM mulgV perm1.
Qed.

Lemma finpermVK π : cancel π^-1 π.
Proof. by move=> a; rewrite -{1}[π]finperm_invK finpermK. Qed.

Lemma finperm_invP : left_inverse finperm_one finperm_inv finperm_mul.
Proof.
move => π. apply/eq_finPermP => a. 
by rewrite finsfunM /= finpermK finsfun1. 
Qed.

Lemma finperm_oneP : left_id 1 finperm_mul.
Proof. move => π. apply/eq_finPermP => a. by rewrite finsfunM /= finsfun1. Qed.

Lemma finperm_invVP : right_inverse finperm_one finperm_inv finperm_mul.
Proof. move => π. by rewrite -(finperm_invP π^-1) finperm_invK. Qed.

Lemma finperm_mulA : associative finperm_mul.
Proof. 
move => π1 π2 π3. apply/eq_finPermP => a /=. by rewrite !finsfunM /= !finsfunM. 
Qed.

Lemma finperm_can2eq π x y :( π x == y) = (x == π^-1 y).
Proof. apply can2_eq; [exact: finpermK | exact: finpermVK]. Qed.

End FinPermTheory.

Section Transpositions.

Implicit Types (a b c : atom).

Local Notation transp a b := [fun z => z with a |-> b, b |-> a].               

Definition tfinsfun a b := 
  @finsfun_of_fun _ _ (@id atom) [fun z => z with a |-> b, b |-> a] [fset a;b].

CoInductive tfinperm_spec a b c : atom -> Type :=
  | TFinpermFirst of c = a : tfinperm_spec a b c b
  | TFinpermSecond of c = b : tfinperm_spec a b c a
  | TFinpermNone of (c != a) && (c != b) : tfinperm_spec a b c c.

Lemma tfinpermP a b c  : 
  tfinperm_spec a b c (tfinsfun a b c).
Proof.
rewrite finsfun_of_funE /=; last first.
  move => {c} c /=. apply contraR. rewrite in_fset2 negb_or 
  => /andP [ c_neq_a c_neq_b]. by rewrite (negbTE c_neq_a) (negbTE c_neq_b).
have [c_eq_a | c_neq_a] := (boolP (c == a)).
  by constructor; apply/eqP.
have [c_eq_b | c_neq_b] := (boolP (c == b)).
  by constructor; apply/eqP.
by constructor; apply /andP. 
Qed.

Lemma inj_tfinsfun a b : 
  injectiveb_finsfun_id (tfinsfun a b).
Proof. 
apply/injectiveb_finsfunP => x y. 
by case: tfinpermP; case: tfinpermP => //; do ?move-> => // ;
move/andP => [neq1 neq2] eq1; do ?move => eq2;
move : neq1 neq2; rewrite ?eq1 ?eq2 eqxx.
Qed.

Definition tfinperm a b :=
  FinPerm (inj_tfinsfun a b).

Lemma tfinpermL a a' :
  (tfinperm a a') a = a'.
Proof. by case: tfinpermP => //; rewrite eqxx. Qed.

Lemma tfinpermR a a' :
  (tfinperm a a') a' = a.
Proof. by case: tfinpermP => //; rewrite eqxx => /andP [ ? ?]. Qed.

Lemma tfinpermNone a a' b :
  (b != a) && (b != a') -> (tfinperm a a') b = b.
Proof. by case: tfinpermP => //; move ->; rewrite eqxx //= andbF. Qed.

Lemma tfinpermC a b : tfinperm a b = tfinperm b a.
Proof.
apply/eq_finPermP => z; case: tfinpermP;
  do ?by move ->; rewrite ?tfinpermL ?tfinpermR.
by move => zNab; rewrite tfinpermNone // andbC.
Qed.


Lemma tfinsfun_id a :
  tfinsfun a a = 1.
Proof.
apply/finsfunP => b; rewrite finsfun1.
by case: tfinpermP; symmetry.
Qed.

Lemma tfinperm_idempotent a b :
  (tfinperm a b) * (tfinperm a b) = 1.
Proof.
apply/eq_finPermP => c.
rewrite finsfunM finsfun1 /=.
case: tfinpermP; case: tfinpermP;
  do ?(by move ->).  
  - by move /andP => [/eqP ? /eqP ?]. 
  - by move /andP => [/eqP ? /eqP ?].
  - by rewrite eqxx => _ /andP [? ?]. 
  - by rewrite eqxx => _ /andP [? ?]. 
Qed.

Lemma tfinperm_conj a a' (π : finPerm) :
  π * (tfinperm a a') = tfinperm (π a) (π a') * π.
Proof.
apply/eq_finPermP => b. rewrite !finsfunM /=.
case: (tfinpermP a a' b) ; do ?move ->; 
rewrite ?tfinpermL ?tfinpermR ?tfinsfun_id ?finsfun1 //.
move/andP => [ab a'b]. have [πb_out] : (π b != π a) && (π b != π a').
  by rewrite !inj_eq; do ?apply finperm_inj; apply/andP.
by rewrite tfinpermNone.
Qed.

Lemma tfinperm_supp x y : finsupp (tfinperm x y) \fsubset [fset x;y].
Proof.
apply/fsubsetP => z. rewrite mem_finsupp in_fset2.
apply contraR => /norP /andP ?. 
by apply/eqP/tfinpermNone.
Qed.

Lemma tfinperm_disj x y S : 
  x \notin S -> y \notin S -> [disjoint S & (finsupp (tfinperm x y))].
Proof.
move => xNS yNS.
rewrite fdisjoint_sym. apply (@fdisjoint_trans _ _ [fset x;y]);
  first exact: tfinperm_supp.                       
apply/fdisjointP => z. rewrite in_fset2 => /orP.
by case => /eqP ->.
Qed.

End Transpositions.

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
     (forall a, a \in (support x.1 :|: support x.2) -> π a = a) -> prodact π x = x.
Proof. 
case: x => x y Hsupp. rewrite /prodact !act_id //= => a asupp; apply Hsupp;
rewrite in_fsetU asupp ?orbT //.
Qed.

Canonical prod_nominal_mixin :=
  @NominalMixin _ prod_nominal_setoid_mixin _ prodact_id.

Canonical prod_nominal_type :=
  NominalType prod_nominal_mixin.

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
exists (SeqSub aA) => //. by rewrite Asupp.
Qed.

(* bricolage *)

Definition code (A : {fset atom}) := fset_keys A.
Definition decode (s : seq atom) := fset s.

Lemma fset_codeK : cancel code decode.
Proof. by move => A; apply/fsetP => a; rewrite in_fset. Qed.

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

Variable (X : nominalType).

(* Definition max (A : {fset atom}) := \max_(a : A) val a.  *)

Fixpoint max_list l := match l with
                             |[::] => 0
                             |a::q => maxn (max_list q) a
                                           end.

Definition fresh_list (l : seq atom) := (max_list l).+1.
Definition fresh (A : {fset atom}) := fresh_list (fset_keys A). 
(* casse l'interface, mais comment faire autrement ? *)

(* Lemma fresh_notin A : fresh A \notin A. *)
(* Proof. *)
(* rewrite/fresh. *)
(* suff : (forall x, x \in A -> x <= max A). *)
(*   move => H. apply contraT. rewrite negbK => /H. by rewrite ltnn. *)
(* move => x xA.  *)
(* have : x = val (SeqSub xA) by []; move ->. *)
(*   apply (@leq_bigmax A val (SeqSub xA)). *)
(* Qed. *)

Lemma freshlist_notin (s : seq atom) : (fresh_list s).+1 \notin s.
Admitted.

Lemma fresh_notin A : fresh A \notin A.
Admitted.

Lemma fresh_subsetnotin (A B: {fset atom}) : A \fsubset B -> fresh B \notin A. 
Proof.
move => /fsubsetP AinclB. have: fresh B \notin B by exact: fresh_notin.
by apply/contra/AinclB.
Qed.

Lemma fresh1U A a : fresh (a |: A) != a.
Proof.
have : fresh (a |: A) \notin [fset a].
  apply/fresh_subsetnotin/fsubsetP => x. rewrite in_fset1 => /eqP ->.
  by rewrite in_fset1U eqxx.
apply contraR. rewrite negbK => /eqP ->. by rewrite in_fset1.
Qed.

Lemma fresh_neq (A : {fset atom}) a : a \in A -> a != fresh A.
Proof. apply contraL => /eqP ->. exact: fresh_notin. Qed.

Lemma fresh_transp (a a' : atom) (x : X)
      (a_fresh_x : a \notin support x) (a'_fresh_x : a' \notin support x) :
  swap a a' \dot x = x.
Proof.
apply act_id => b bsuppx. case: tfinpermP => //= b_eq; rewrite b_eq in bsuppx. 
  by rewrite bsuppx in a_fresh_x.
by rewrite bsuppx in a'_fresh_x.
Qed.

Lemma fresh_perm (π : finPerm) (x : X) : 
  [disjoint (support x) & finsupp π] -> π \dot x = x.
Proof.
move => /fdisjointP disj_x_π.  
apply act_id => a /disj_x_π.
exact: finsfun_dflt.
Qed.

End Freshness.

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

Variables (X : nominalType).
Implicit Types (x : X).

(* hypothèse équivalente à : "support x" est le plus petit support de x *)
Hypothesis strong_support : 
  forall x π, π \dot x = x -> (forall a : atom, a \in support x -> π a == a).

Lemma equi_support : equivariant1 (@support X).
Proof.
move => π x.
wlog suff : x π / im π (support x) \fsubset support (π \dot x).  
  move => Hsuff; apply/eqP; rewrite eqEfsubset; apply/andP; split; last by apply Hsuff.
  rewrite -(actVK π (support (π \dot x))) -{2}[x](actK π x);
  exact/im_subset/Hsuff.
apply/fsubsetP => a /imfsetP [b bx] ->. apply contraT => πbNπx. 
pose c := fresh (val b |: im π^-1 (support (π \dot x))).
have : swap (val b) c \dot x = x.
  apply (@act_inj _ π). rewrite -actM tfinperm_conj actM fresh_transp //. 
  rewrite -(actVK π (support (π \dot x))); rewrite mem_im;
    last exact: finperm_inj.  
  by apply fresh_subsetnotin; rewrite fsubsetU1.
have {bx} bx : val b \in support x. by apply valP.
move/strong_support => H. move: (H (val b) bx).
rewrite tfinpermL => /eqP cvalb. move: (fresh1U  (im π^-1 (support (π \dot x))) (val b)).
by rewrite-/c -cvalb eqxx. 
Qed.

Lemma mem_im_supp (π : finPerm) a x : 
  π a \in (support x) = (a \in support (π^-1 \dot x)).
Proof.
by rewrite -[a \in _](mem_imperm π) equi_support -actM finperm_invVP act1. 
Qed.

Lemma supp_fx (Y : nominalType) (f : X -> Y) (S : {fset atom})  (fs_f : function_support1 f S) : forall (x : X), support (f x) \fsubset (S :|: support x).
Proof.
move => x.
apply/fsubsetP => a. apply contraLR => aNS.
have test : (swap a (fresh (a |: support x))) \dot x = x.
  admit.

Abort All.


End StrongSupport.


Section SomeAny.

Variable (X Y : nominalType).

Definition new (P : atom -> Prop) :=
  exists A : {fset atom}, forall a, a \notin A -> P a.

Notation "\new a , P" := (new (fun a:atom => P))
   (format "\new  a ,  P", at level 200).
Notation "a # x" := (a \notin support x)
                      (at level 0).

Theorem some_any (R : atom -> X -> Prop) :
  equivariant_prop R ->
  forall x : X, [/\
      (forall a : atom , a # x -> R a x) -> (\new a, R a x),
      (\new a, R a x) ->  R (fresh (support x)) x,
      R (fresh (support x)) x -> (exists2 a, a # x & R a x) &
      (exists2 a, a # x & R a x)
      -> (forall a, a # x -> R a x)
    ].
Proof.
move => Requi; split; first by exists (support x).
  - move => [S aNSR]. 
    apply/(Requi (swap (fresh (support x)) (fresh ((support x) :|: S)))).
    rewrite swapL [_ \dot x]fresh_transp ?fresh_notin ?fresh_subsetnotin ?fsubsetUl //.
    apply/aNSR/fresh_subsetnotin. by rewrite fsubsetUr.
  - move => Rfresh. exists (fresh (support x)) => //. by apply fresh_notin.
  - move => [a a_fresh_x rax] a' a'_fresh_x.
    case: (eqVneq a a'); first by move <-.
    move => aa'. 
    rewrite -[a'](tfinpermL a a') -[x](fresh_transp a_fresh_x a'_fresh_x) //. 
    by apply Requi.
Qed.

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
  forall x: X, R (fresh (support x)) x <-> \new a, R a x. 
Proof.
move=> Requi x. have [fn nf nh ef] := some_any Requi x. 
by split => [/nh/ef/fn | /nf]. 
Qed.

End SomeAny.

Notation "\new a , P" := (new (fun a:atom => P))
   (format "\new  a ,  P", at level 200).
Notation "a # x" := (a \notin support x)
                      (at level 0).

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
    |rApp t1 t2 => term_support t1 :|: term_support t2
    |rLambda a t => a |: term_support t
  end.

Fixpoint fv t :=
  match t with
      |rVar a => [fset a]
      |rApp t1 t2 => fv t1 :|: fv t2
      |rLambda a t => fv t :\ a
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
       let z := fresh (support a :|: support u :|: (support a' :|: support u')) in 
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
  let z := fresh (support x :|: support t :|: (support y :|: support u)) in
  alpha (swap x z \dot t) (swap y z \dot u).
Proof. by rewrite /alpha /= raw_depth_perm. Qed.

Inductive alpha_spec t1 t2 : rawterm -> rawterm -> bool -> Type :=
  | AlphaVar a & t1 = rVar a & t2 = rVar a: alpha_spec t1 t2 (rVar a) (rVar a) true
  | AlphaApp u1 v1 u2 v2 & t1 = rApp u1 v1 & t2 = rApp u2 v2 :
      alpha_spec t1 t2 (rApp u1 v1) (rApp u2 v2) (alpha u1 u2 && alpha v1 v2)
  | AlphaLam a1 u1 a2 u2 & t1 = rLambda a1 u1 & t2 = rLambda a2 u2 :
      alpha_spec t1 t2 (rLambda a1 u1) (rLambda a2 u2)
                 (let b := fresh ([fset a1; a2] :|: support t1 :|: support t2) in
                            alpha (swap a1 b \dot u1) (swap a2 b \dot u2)).

(* Lemma equi_alpha π : {mono actN π : t1 t2 / alpha t1 t2}.
Proof.
move =>t1 t2 /=; rewrite /alpha raw_depth_perm.
elim: t1 t2 => [x|u v|x u] [y|u' v'|y u'] //=. [a a'|t'1 iht'1 t'2 iht'2 t1|] //;
rewrite /alpha ?raw_depth_perm.
  - by apply: (inj_eq (@finperm_inj π)).
  - move => bla. *)
(*
Lemma alphaP t1 t2 : alpha_spec t1 t2 (alpha t1 t2).

Lemma alpha_ind (P : rawterm -> rawterm -> Prop) :
(forall a : atom, P (rVar a) (rVar a)) ->
(forall u v u' v' : rawterm, alpha_spec u u' -> P u u' ->
                             alpha_spec v v' -> P v v' -> 
                             P (rApp u v) (rApp u' v')) ->
(forall (x y : atom) u u',
   (\new z, alpha_spec (swap x z \dot u) (swap y z \dot u')) ->
   (\new z, P (swap x z \dot u) (swap y z \dot u')) ->
 P (rLambda x u) (rLambda y u')) ->
forall t t' : rawterm, alpha_spec t t' -> P t t'.
Proof.
move=> Pvar Papp Plam t t'.
move: {-1}(raw_depth t) (leqnn (raw_depth t)) => n.
elim: n t t' => [|n ihn] t t'.
  by rewrite leqn0 => /eqP dt att'; case: att' dt.
rewrite leq_eqVlt => /predU1P [dt att'|/ihn]; last exact.
case: att' dt => //.
  move=> u v u' v' auu' avv' /= [duv].
  by apply: Papp => //; apply: ihn => //; rewrite -duv (leq_maxl, leq_maxr).
move=> x y u u' auu' [du]; apply: Plam => //.
case: auu' => S HS; exists S => z zNS.
apply: ihn. by rewrite raw_depth_perm du. by apply HS.
Qed.
*)
                 
(* Lemma equi_alpha t t' π : alpha_spec t t' <-> alpha_spec (π \dot t) (π \dot t'). 
Proof.
wlog suff : t t' π / alpha_spec t t' -> alpha_spec (π \dot t) (π \dot t') => [hw|].
  split; first exact: hw.
  move/(hw (π \dot t) (π \dot t') π^-1). by rewrite -!actM finperm_invP !act1.
move => /alpha_ind E. elim/E : {t t' E} _ => 
  [x|u v u' v' uαu' πuαπu' vαv' πvαπv' | x y u u' Hu Hπu].
  - by constructor.
  - by  constructor. 
  - case: Hπu => S HS. constructor. exists (im π S) => z zNS.
    rewrite -!actM -[z](finpermVK π z) -!tfinperm_conj actM; rewrite actM.
    apply HS. rewrite -(@mem_im _ _ (@id atom) π S) ?finpermVK //.
    exact: finperm_inj.                                                
Qed.

*)

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
set a' := fresh _. set a := fresh _.
rewrite -[a'](finpermVK π) -!actM -!tfinperm_conj => ru_lt_n. 
have u_fix : swap a (π^-1 a') \dot u = u.
  apply/fresh_transp. apply/fresh_subsetnotin/fsubsetU. 
  rewrite fsubsetU // fsubsetAA orbT //. rewrite mem_im_supp;
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
apply/alpha_lamP. exists (S :|: S') => a.
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

(* Inductive term := *)
(*   |BVar : nat ->  term *)
(*   |FVar : atom -> term *)
(*   |App : term -> term -> term *)
(*   |Lambda : term -> term. *)

(* Fixpoint open_rec (k : nat) (u : term) (t : term) {struct t} : term := *)
(*   match t with *)
(*     | BVar i => if k == i then u else (BVar i) *)
(*     | FVar x  => FVar x *)
(*     | Lambda t  => Lambda (open_rec (k.+1) u t) *)
(*     | App t1 t2 => App (open_rec k u t1) (open_rec k u t2) *)
(*   end. *)

(* Definition open t u := open_rec 0 u t. *)

(* Notation "{ k ~> u } t" := (open_rec k u t) (at level 67). *)
(* Notation "t ^^ u" := (open t u) (at level 67). *)
(* Notation "t ^ x" := (open t (FVar x)). *)

(* Eval compute in open (App (Lambda (App (BVar 1) (BVar 0))) (BVar 0)) (FVar 7). *)

(* Fixpoint pi (t : rawterm) : term := *)
(*   let fix aux (l : seq atom) (u : rawterm) := *)
(*       match u with  *)
(*         |rVar x => if x \in l then BVar (index x l) else FVar (addn x (size l)) *)
(*         |rApp t1 t2 => App (aux l t1) (aux l t2) *)
(*         |rLambda x u' => Lambda (aux (x::l) u') *)
(*       end *)
(*         in *)
(*   aux [::] t. *)

(* Lemma rAppK t1 t2 : pi (rApp t1 t2) = App (pi t1) (pi t2). *)
(* Proof. by elim: t1; elim: t2 => //. Qed. *)

(* Fixpoint fvars (t : term) : seq atom := *)
(*   match t with *)
(*       |BVar x => [::] *)
(*       |FVar x => [::x] *)
(*       |App t1 t2 => (fvars t1) ++ (fvars t2) *)
(*       |Lambda t => fvars t *)
(*       end. *)

(* Fixpoint depth (t : term) : nat := *)
(*   match t with *)
(*       |BVar n => 0 *)
(*       |FVar x => 0 *)
(*       |App t1 t2 => (maxn (depth t1) (depth t2)).+1 *)
(*       |Lambda t => (depth t).+1 *)
(*   end. *)

(* Fixpoint wf_rec n (t : term) :=  *)
(*   let z := fresh_list (fvars t) in  *)
(*       match n, t with *)
(*         |_, BVar m => false *)
(*         |_, FVar x => true *)
(*         |S n, App t1 t2 => (wf_rec n t1) && (wf_rec n t2) *)
(*         |S n, Lambda t => wf_rec n (t^z) *)
(*         |_,_ => false *)
(*       end. *)

(* Definition wf (t : term) := wf_rec (depth t) t. *)

(* Lemma wf_recE n t : (depth t <= n) -> wf_rec n t = wf t. *)
(* Proof. *)
(* rewrite /wf; move: {-2}n (leqnn n). *)
(* elim: n t => //= => [t n|n IH [m|x|t1 t2|t]].  *)
(*   by rewrite leqn0 => /eqP ->; rewrite leqn0 => /eqP ->. *)
(* rewrite /=.                *)
(*   rewrite !ltnS geq_max => lmn /andP [um vm].  *)
(*   rewrite !ihn // ?(leq_maxl, leq_maxr) ?geq_max *)
(*              ?(leq_trans um, leq_trans vm) //. *)
(* rewrite !ltnS => lmn um. by rewrite ihn // ?raw_depth_perm.  *)
(* Qed. *)



(* Lemma wf_app t1 t2 : wf (App t1 t2) = (wf t1 && wf t2). *)
(* Proof. *)
(* move: {-1}(depth (App t1 t2)) (leqnn (depth (App t1 t2))) => n. *)
(* elim : n t1 t2 => [t1 t2|n IH t1 t2]. *)
(*   by rewrite ltn0. *)



(* Definition wf_term := sig wf. *)
(* Coercion wf_term_term (t : wf_term) : term := (val t). *)

(* Fixpoint repr (t : wf_term) : rawterm := *)
(*   let fix aux (t : term) (l : seq atom) (bvars : seq atom) := *)
(*       match t with  *)
(*         |BVar x => rVar (nth x bvars x) *)
(*         |FVar x => rVar x *)
(*         |App t1 t2 => rApp (aux t1 l bvars) (aux t2 l bvars) *)
(*         |Lambda t => let x := (fresh_list l) in rLambda x (aux t (x::l) (x::bvars)) *)
(*       end *)
(*   in aux t (fvars t) [::]. *)

(* Lemma wf_pi (t : rawterm) : wf (pi t). *)
(* Proof. *)
(* elim: t => //. *)
(*  move => t wft u wfu. rewrite rAppK. rewrite /=. *)

(* Lemma reprK : cancel repr pi. *)
(* Proof. *)
(* elim => [a|||].  *)
(* move => t. *)

    
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
rewrite in_fsetU /= in_fset1 => /norP [x_neq_y x_fresh_t] ->.
unlock Lambda; apply/eqP; rewrite -alpha_eqE alpha_lamE /= alpha_eqE. 
set z := fresh _.
rewrite -!pi_equivariant !reprK.
have xzu : swap x z \dot u = u.  
  apply/fresh_transp => //; apply/fresh_subsetnotin.
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

Lemma term_altind_subproof (X : nominalType) (P : term -> X -> Prop) :
  (forall x C, P (Var x) C) ->
  (forall C t1 t2, (forall D, P t1 D) -> (forall D, P t2 D) -> 
                   P (App t1 t2) C) ->
  (forall x t C, x # C -> (forall D, P t D) -> P (Lambda x t) C) ->
  forall u π C, P (π \dot u) C.
Proof.
move => HVar HApp HLam u.
elim/term_ind : u => [x π C|t1 t2 IHt1 IHt2 π C|].
  - rewrite Var_equiv. by apply HVar.
  - rewrite App_equiv. by apply HApp.
  - move => x t HPt π C.
    rewrite Lam_equiv. have [xfreshC | xNfreshC] := boolP ((π \dot x) # C).
      by apply HLam.
    pose z := fresh (support C :|: support (π \dot x) :|: support (π \dot t)).
    suff : (Lambda (π \dot x) (π \dot t)) = 
           (Lambda z (swap (π \dot x) z \dot (π \dot t))).
      move->; apply HLam; [|rewrite -actM; exact: HPt]. 
      apply/fresh_subsetnotin. by rewrite -fsetUA fsubsetUl.
    apply/sym_eq/eq_lam; last by rewrite tfinpermC.
    apply fresh_subsetnotin. by rewrite -fsetUA fsubsetUr.
Qed.

Lemma term_altind (X : nominalType) (P : term -> X -> Prop) C :
  (forall x C, P (Var x) C) ->
  (forall C t1 t2, (forall D, P t1 D) -> (forall D, P t2 D) -> 
                   P (App t1 t2) C) ->
  (forall x t C, x # C -> (forall D, P t D) -> P (Lambda x t) C) ->
  forall u, P u C.
Proof. 
move => HVar HApp HLam u. rewrite -[u]act1 => *. 
exact: term_altind_subproof. 
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
set z := fresh _.
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
pose z := fresh S.
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
    |S n, rLambda x u => let z := fresh ((S1 :|: S2 :|: S3) :|: (support x :|: support t)) in 
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
set z := fresh _.
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
  [disjoint x |: A & B] = ((x \notin B) && [disjoint A & B]%fset).
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
    set a := fresh _; set b := fresh _.
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
    pose m := fresh ((S :|: S1) :|: (S2 :|: S3 ) :|: (support (π \dot v) :|: support u) :|:
                     (support (f3 a t1 (term_altrect t1)) :|:
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
Qed.

Lemma f3α x t y u :
  x \notin S1 :|: S2 :|: S3 -> y \notin S1 :|: S2 :|: S3 -> Lambda x t = Lambda y u ->
  f3 x t (term_altrect t) = f3 y u (term_altrect u).
Proof.
move => xNS1S2S2 yNS1S2S3. 
unlock Lambda => /eqP. rewrite -alpha_eqE => /alpha_lamP [S HS].
pose z := fresh (S1 :|: S2 :|: S3 :|: S :|:
                 support (f3 x t (term_altrect t)) :|:
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
Qed.

Lemma term_altrect_LamE x t :
  x \notin (S1 :|: S2 :|: S3) -> 
  @term_altrect (Lambda x t) = f3 x t (term_altrect t).
Proof.
rewrite in_fsetU in_fsetU => /norP [/norP [xNS1 xNS2]] xNS3.
have [y [u [[S HS] repr_xt]]] := LambdaK x t.   
rewrite/term_altrect depth_lam /= repr_xt.
set a := fresh _. 
move: (HS _ (fresh_notin S)) => yzu_xzt.
have depth_tu : depth t = depth (\pi (swap y a \dot u)).
  rewrite -pi_equivariant depth_perm.
  rewrite -(depth_perm _ (swap x (fresh S))) -yzu_xzt.
  by rewrite -pi_equivariant depth_perm.
have aNS3 : a \notin S3 by admit.
rewrite {1}depth_tu.
apply f3α => //. admit. admit.
rewrite (@eq_lam a _ y (\pi u)).
  move: (congr1 \pi_term repr_xt).
  by rewrite reprK rLambdaK.
admit.
rewrite -pi_equivariant. admit.
Qed.

End EliminationPrinciples.

Section Subst.


Variables (x : atom) (t : term).

Definition dflt := Var 0.

Definition subst_f1 y := if x == y then t else Var y.
Definition subst_f2 (t1 t2 : term) subst_t1 subst_t2 :=
  App subst_t1 subst_t2.
Definition subst_f3 x (t : term) subst_t := Lambda x subst_t.

Lemma if_equivariant (X : nominalType) (b : bool) (t1 t2 : X) π :
  (π \dot (if b then t1 else t2)) = (if b then (π \dot t1) else (π \dot t2)). 
Proof. by case: b. Qed.

Lemma support_subst_f1 : function_support1 subst_f1 (x |: support t).
Proof.
move=>π; rewrite fset1_disjoint => /andP [xNπ disj_t_π] y.
have xNπinv : x \notin finsupp π^-1 by [].
by rewrite/subst_f1 if_equivariant Var_equiv atomactE [_ == π _]eq_sym 
finperm_can2eq eq_sym (finsfun_dflt xNπinv) (fresh_perm disj_t_π).
Qed.

Lemma support_subst_f2 : function_support4 subst_f2 fset0.
Proof.
move => π _ t1 t2 u1 u2. 
by rewrite /subst_f2 App_equiv.
Qed.

Lemma support_subst_f3 : function_support3 subst_f3 fset0.
Proof.
move => π _ y u v.
by rewrite /subst_f3 Lam_equiv.
Qed.

Lemma FCB_f3 : FCB subst_f3.
Proof.
exists (@fset0 nat_KeyType) => y u v.
admit.
Qed.

Definition subst := term_altrect subst_f1 subst_f2 subst_f3 (x |: support t) fset0 fset0 dflt.

Lemma subst_VarE y : subst (Var y) = if x == y then t else Var y. 
Proof.
by rewrite/subst term_altrect_VarE /subst_f1.
Qed.

Lemma subst_AppE t1 t2 : subst (App t1 t2) = App (subst t1) (subst t2).
Proof.
by rewrite/subst term_altrect_AppE /subst_f2.
Qed.

Lemma subst_LamE y u : subst (Lambda y u) = Lambda y (subst u).
Proof.
rewrite/subst term_altrect_LamE /subst_f3 //.
  exact: support_subst_f1.
  exact: support_subst_f2.
  exact: support_subst_f3.
