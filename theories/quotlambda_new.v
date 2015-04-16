Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq.
Require Import bigop fintype finfun finset generic_quotient perm.
Require Import tuple.
Require Import fingroup.
Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope finperm_scope with fperm.
Local Open Scope finperm_scope.
Local Open Scope fset.

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
by case: (finsfunP _ a) => [/negPf -> //|af]; apply: (f_stable (SeqSub af)).
Qed.

Lemma perm_stable (π : finPerm) (S : {fset atom}) :
  finsupp π \fsubset S -> forall (a : atom), a \in S -> π a \in S. 
Proof.
move=> /fsubsetP S_surfinsupp a; case:finsfunP; first by []. 
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
by apply eq_finsfunP.
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

Let ffun_of_finPerm (π : finPerm) (S : {fset atom}) 
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

Section FinPermSpec.

CoInductive finPerm_spec (π : finPerm) (a : atom) : atom -> bool -> Type :=
  | FinPermOut : a \notin finsupp π -> finPerm_spec π a a false
  | FinPermIn  (aπ : a \in finsupp π) : 
      finPerm_spec π a (val (can_perm_of_finPerm π (SeqSub aπ))) true.

Lemma finPermP (π : finPerm) (a : atom) : finPerm_spec π a (π a) (a \in finsupp π).
Proof.
case:finsfunP; first by exact: FinPermOut.
move => aπ. suff: π a = (val (can_perm_of_finPerm π (SeqSub aπ))).
  by move ->; apply: FinPermIn.
have t : π a = val (SeqSub (perm_stable (fsubsetAA (finsupp π)) aπ)) by [].
rewrite t. congr val. by rewrite perm_of_finPermE.
Qed.

End FinPermSpec.

Section FinPermInvDef.

Variable (π : finPerm).

Definition finmap_inv_subproof :=
  FinMap [ffun a : finsupp π => val ((perm_inv (can_perm_of_finPerm π)) a)].

Fact finmap_can_subproof : 
  [forall a: domf (finmap_inv_subproof) , finmap_inv_subproof a != @id atom (val a)].
Proof.
apply/forallP => x. rewrite ffunE val_eqE.
pose p := can_perm_of_finPerm π. rewrite (can2_eq (permKV p) (permK p)).  
rewrite perm_of_finPermE -val_eqE eq_sym -mem_finsupp. exact: ssvalP.
Qed.

Definition finsfun_inv_subproof := FinSFun finmap_can_subproof.

Fact injective_finsfun_subproof : injectiveb_finsfun_id finsfun_inv_subproof.
Proof.
apply/andP. split.
  apply/injectiveP => a b. rewrite !ffunE /=.
  case: finsfunP; case: (finsfunP finsfun_inv_subproof (ssval b)); rewrite !ssvalP //=. 
  rewrite/fun_of_finsfun !in_fnd ?ssvalP //= => bπ aπ _ _.
  rewrite !ffunE => /eqP. rewrite val_eqE => /eqP πa_eq_πb.
    suff :  {| ssval := ssval a; ssvalP := aπ |} = {| ssval := ssval b; ssvalP := bπ |}.  
    by move/(congr1 val) => /= ; apply/val_inj. 
  apply/eqP. rewrite -(inj_eq (@perm_inj _ (perm_inv (can_perm_of_finPerm π)))).
  by apply/eqP.
apply/forallP => a. rewrite/fun_of_finsfun. rewrite in_fnd; first by apply: valP.
move => aπ /=. rewrite ffunE. exact: valP.
Qed.

Definition finPerm_inv := 
  FinPerm injective_finsfun_subproof.

(* l'égalité finsupp π = finsupp π^-1 est maintenant définitionnelle *)

End FinPermInvDef. 

Local Notation "p ^-1" := (finPerm_inv p) : finperm_scope.

Lemma perm_invK : involutive finPerm_inv.
Proof.
move => π. apply/eq_finPermP => a. 
case: (finPermP π a) => [ aNπ | aπ].
  rewrite finsfun_dflt //.  by rewrite -inv_support -inv_support.
case: finPermP; first by rewrite -inv_support -inv_support aπ.
move => ainvinvπ. 

Lemma permK (π : finPerm) : cancel π π^-1.
Proof.
move => a. case:(finsfunP π a) => /= [aπ| aNπ]. 
  rewrite finsfun_dflt //.
  pose p := (perm_of_finPerm (fsubsetAA (finsupp π)))^-1%g. move: aπ. 
  apply contra.  exact (fsubsetP (finsfun_of_perm_incl p) a).
rewrite finsfun_of_permE in_fun_of_ffun. 
  apply/perm_stable => //=. by apply fsubsetAA. 
move => πa_supp. rewrite ffunE. 

*)