From Ssreflect
Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq fintype.

From MathComp
Require Import bigop  finfun finset generic_quotient perm tuple fingroup.
Require Import finmap.
Require Import finsfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope finperm_scope with fperm.
Local Open Scope finperm_scope.
Local Open Scope fset.
Local Open Scope quotient_scope.

Definition atom := nat.

Import Key.Exports.

Section FinPermDef.

Variable (K : keyType).

Record finPerm := FinPerm {
  perm_of :> finsfun (@id K);
  _ : injectiveb_finsfun_id  perm_of
}.

Definition finperm_of (_ : phant K) := finPerm.

Lemma finperm_inj (π : finPerm) : injective π.
Proof. by case:π => *; apply/injectiveb_finsfunP. Qed.

Lemma in_permsupp (π : finPerm) : {mono π : a / a \in finsupp π}.
Proof. 
move=> a; case: π => f /=.
move=> /andP [/finsfun_injective_inP f_inj_in /forallP f_stable].
by case: (finsuppP _ a) => [/negPf -> //|af]; apply: (f_stable (FSetSub af)).
Qed.

Lemma perm_stable (π : finPerm) (S : {fset K}) :
  finsupp π `<=` S -> forall (a : K), a \in S -> π a \in S. 
Proof.
move=> /fsubsetP S_surfinsupp a; case:finsuppP; first by []. 
by move => a_supp aS; apply/S_surfinsupp/(monoW (@in_permsupp _)).
Qed.

Definition eq_finPerm (π π' : finPerm) :=
    [forall a: (finsupp π `|` finsupp π'), π (val a) == π' (val a)].

Lemma eq1_finPermP (π π' : finPerm) : reflect (π =1 π') (eq_finPerm π π').
Proof.
apply: (iffP idP); last first.
  move => π_eq_π'. apply/forallP => *. by apply/eqP/π_eq_π'.
move => /forallP π_eq_π' a. 
have [aππ'|aNππ'] := boolP (a \in (finsupp π `|` finsupp π')).
  by apply/eqP/(π_eq_π' (FSetSub aππ')).
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

Notation "{finperm K }" := (@finperm_of _ (Phant K)) : type_scope.

Section PermFinPerm.

Variable (K : keyType).

Definition ffun_of_finPerm (π : {finperm K}) (S : {fset K}) 
           (supp_incl_S : finsupp π `<=` S) := 
  [ffun x:S => FSetSub (perm_stable supp_incl_S (fsvalP x))].

Fact perm_of_finPerm_subproof (π : {finperm K}) (S : {fset K}) 
      (supp_incl_S : finsupp π `<=` S) : injectiveb (ffun_of_finPerm supp_incl_S). 
Proof.
apply/injectiveP => a b; rewrite !ffunE; move/(congr1 val) => πa_eq_πb. 
by apply/val_inj/(finperm_inj πa_eq_πb).
Qed.

Definition perm_of_finPerm (π : {finperm K}) (S : {fset K}) 
           (supp_incl_S : finsupp π `<=` S) := 
  Perm (perm_of_finPerm_subproof supp_incl_S).

Definition can_perm_of_finPerm (π : {finperm K}) := 
  perm_of_finPerm (fsubsetAA (finsupp π)).

Lemma perm_of_finPermE (π : {finperm K}) (S : {fset K}) 
      (supp_incl_S : finsupp π `<=` S) :
  forall a : S, perm_of_finPerm supp_incl_S a = FSetSub (perm_stable supp_incl_S (fsvalP a)).
Proof. move => a. by rewrite/perm_of_finPerm -pvalE /ffun_of_finPerm /= ffunE. Qed.

End PermFinPerm.

Section FinPermSpec.

Variable (K : keyType).
  
Lemma finPerm_can (π : {finperm K}) (a : K) (aπ : a \in finsupp π) :
  π a = (val (can_perm_of_finPerm π (FSetSub aπ))).
Proof.
have t : π a = val (FSetSub (perm_stable (fsubsetAA (finsupp π)) aπ)) by []. 
by rewrite t perm_of_finPermE. 
Qed.

CoInductive finPerm_spec (π : {finperm K}) (a : K) : K -> bool -> Type :=
  | FinPermOut : a \notin finsupp π -> finPerm_spec π a a false
  | FinPermIn  (aπ : a \in finsupp π) : 
      finPerm_spec π a (val (can_perm_of_finPerm π (FSetSub aπ))) true.

Lemma finPermP (π : {finperm K}) (a : K) : finPerm_spec π a (π a) (a \in finsupp π).
Proof.
case:finsuppP; first by exact: FinPermOut.
move => aπ. suff: π a = (val (can_perm_of_finPerm π (FSetSub aπ))).
  by move ->; apply: FinPermIn.
exact: finPerm_can.
Qed.

End FinPermSpec.

Section FinPermInvDef.

Variables (K : keyType) (π : {finperm K}).

Let p := can_perm_of_finPerm π.
Let inv_p_ffun := [ffun a : finsupp π => val ( p^-1%g a)].

Fact can_p_subproof : [forall a : finsupp π ,  inv_p_ffun a != val a].
Proof.
apply/forallP => a. rewrite ffunE val_eqE.
rewrite (can2_eq (permKV p) (permK p)).
rewrite perm_of_finPermE eq_sym -mem_finsupp. exact: fsvalP.
Qed.

Definition finsfun_invp_subproof := @finsfun_of_can_ffun _ _ (@id K) _ _ can_p_subproof.

Fact injective_finsfun_subproof : injectiveb_finsfun_id finsfun_invp_subproof.
Proof.
apply/andP. split; last first.
  apply/forallP => a. rewrite !finsfun_of_can_ffunE; first by apply: valP.
  move => aπ /=. rewrite ffunE. exact: valP.
apply/injectiveP => a b. rewrite !ffunE !finsfun_of_can_ffunE; rewrite ?ssvalP //=.
move => bπ aπ. rewrite !ffunE => pa_eq_pb.
suff: {| fsval := fsval a; fsvalP := aπ |} = {| fsval := fsval b; fsvalP := bπ |}.
  by move/(congr1 val) => /=; apply/val_inj. 
apply/eqP. rewrite -(inj_eq (@perm_inj _ (perm_inv (can_perm_of_finPerm π)))).
exact/eqP/val_inj.
Qed.

Definition finperm_inv := 
  FinPerm injective_finsfun_subproof.

Lemma finperm_one_subproof : injectiveb_finsfun_id (@finsfun_one K).
Proof. by apply/injectiveb_finsfunP/inj_finsfun_one. Qed.

Definition finperm_one := FinPerm finperm_one_subproof.

End FinPermInvDef. 

Section FinPermMulDef.

Variable (K : keyType).

Lemma finperm_mul_subproof (π π' : {finperm K}) :
  injectiveb_finsfun_id (@finsfun_comp _ π π').
Proof. apply/injectiveb_finsfunP/inj_finsfun_comp; by apply finperm_inj. Qed.

Definition finperm_mul (π π' : {finperm K}) :=
  FinPerm (finperm_mul_subproof π π').

End FinPermMulDef.

Notation "1" := (finperm_one).
Notation "π * π'" := (@finperm_mul _ π π').
Notation "π ^-1" := (@finperm_inv _ π) : finperm_scope.
Notation "π ~" := (@can_perm_of_finPerm _ π) 
  (at level 0) : finperm_scope.  

Section FinPermTheory.

Variable (K : keyType).
  
Implicit Types (π : {finperm K}) (a : K).

Lemma can_inv π : π^-1~ = π~^-1%g.
Proof.
apply permP => a. rewrite perm_of_finPermE.
apply val_inj => /=. rewrite finsfun_of_can_ffunE ffunE. 
suff : {| fsval := fsval a; fsvalP := fsvalP a |} = a by move ->.
by apply val_inj.
Qed.

Lemma finperm_invK : involutive (@finperm_inv K).
Proof.
move => π. apply/eq_finPermP/eq1_finPermP/forallP. 
rewrite fsetUid => a. rewrite !finPerm_can; do ?apply: valP.
move => aπ ainvinvπ. rewrite val_eqE can_inv can_inv invgK.
suff : ainvinvπ = aπ by move ->.
exact: bool_irrelevance.
Qed.

Lemma myvalK  (S : {fset K}) (a : S) aS :
  {| fsval := val a;
     fsvalP := aS |} = a.
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

Lemma finperm_invP : left_inverse (1 K) (@finperm_inv K) (@finperm_mul K).
Proof.
move => π. apply/eq_finPermP => a. 
by rewrite finsfunM /= finpermK finsfun1. 
Qed.

Lemma finperm_oneP : left_id (1 K) (@finperm_mul K).
Proof. move => π. apply/eq_finPermP => a. by rewrite finsfunM /= finsfun1. Qed.

Lemma finperm_invVP : right_inverse (1 K) (@finperm_inv K) (@finperm_mul K).
Proof. move => π. by rewrite -(finperm_invP π^-1) finperm_invK. Qed.

Lemma finperm_mulA : associative (@finperm_mul K).
Proof. 
move => π1 π2 π3. apply/eq_finPermP => a /=. by rewrite !finsfunM /= !finsfunM. 
Qed.

Lemma finperm_can2eq π x y :( π x == y) = (x == π^-1 y).
Proof. apply can2_eq; [exact: finpermK | exact: finpermVK]. Qed.

End FinPermTheory.

Section Transpositions.

Variable (K : keyType).  
  
Implicit Types (a b c : K).

Local Notation transp a b := [fun z => z with a |-> b, b |-> a].               

Definition tfinsfun a b := 
  @finsfun_of_fun _ _ (@id K) [fun z => z with a |-> b, b |-> a] [fset a;b].

CoInductive tfinperm_spec a b c : K -> Type :=
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
  tfinsfun a a = (1 K).
Proof.
apply/finsfunP => b; rewrite finsfun1.
by case: tfinpermP; symmetry.
Qed.

Lemma tfinperm_id a :
  tfinperm a a = (1 K).
Proof.
apply/eq_finPermP => x /=.
by rewrite tfinsfun_id /=.
Qed.

Lemma tfinperm_idempotent a b :
  (tfinperm a b) * (tfinperm a b) = (1 K).
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

Lemma tfinperm_conj a a' (π : {finperm K}) :
  π * (tfinperm a a') = tfinperm (π a) (π a') * π.
Proof.
apply/eq_finPermP => b. rewrite !finsfunM /=.
case: (tfinpermP a a' b) ; do ?move ->; 
rewrite ?tfinpermL ?tfinpermR ?tfinsfun_id ?finsfun1 //.
move/andP => [ab a'b]. have [πb_out] : (π b != π a) && (π b != π a').
  by rewrite !inj_eq; do ?apply finperm_inj; apply/andP.
by rewrite tfinpermNone.
Qed.

Lemma tfinperm_conj_imL a a' (π : {finperm K}) :
  π * (tfinperm a (π^-1 a')) = tfinperm (π a) a' * π.
Proof. by rewrite tfinperm_conj finpermVK. Qed.

Lemma tfinperm_conj_imR a a' (π : {finperm K}) :
  π * (tfinperm (π^-1 a) a') = tfinperm a (π a') * π.
Proof. by rewrite tfinperm_conj finpermVK. Qed.

Lemma tfinperm_supp x y : finsupp (tfinperm x y) `<=` [fset x;y].
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
