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
case:finsfunP; first by exact: FinPermOut.
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
apply/andP. split.
  apply/injectiveP => a b. rewrite !ffunE !finsfun_of_can_ffunE; rewrite ?ssvalP //=.
  move => bπ aπ. rewrite !ffunE => pa_eq_pb.
  suff: {| ssval := ssval a; ssvalP := aπ |} = {| ssval := ssval b; ssvalP := bπ |}.
    by move/(congr1 val) => /=; apply/val_inj. 
  apply/eqP. rewrite -(inj_eq (@perm_inj _ (perm_inv (can_perm_of_finPerm π)))).
  rewrite -val_eqE. by apply/eqP.
apply/forallP => a. rewrite !finsfun_of_can_ffunE; first by apply: valP.
move => aπ /=. rewrite ffunE. exact: valP.
Qed.

Definition finPerm_inv := 
  FinPerm injective_finsfun_subproof.

(* l'égalité finsupp π = finsupp π^-1 est maintenant définitionnelle *)

End FinPermInvDef. 

Local Notation "p ^-1" := (finPerm_inv p) : finperm_scope.

Section Theory.

Implicit Types (π : finPerm) (a : atom).  

Lemma can_inv π : can_perm_of_finPerm π^-1 = (can_perm_of_finPerm π)^-1%g.
Proof.
apply permP => a. rewrite perm_of_finPermE.
apply val_inj => /=. rewrite finsfun_of_can_ffunE; first by apply: valP.
move => aπ /=. rewrite ffunE.  congr ssval. 
suff : {| ssval := ssval a; ssvalP := aπ |} = a by move ->.
by apply val_inj.
Qed.

Lemma perm_invK : involutive finPerm_inv.
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

Lemma permK (π : finPerm) : cancel π π^-1.
Proof.
move => a. case: (finPermP π a) => [aNπ | aπ].
  by rewrite finsfun_dflt.
rewrite finPerm_can; first by apply: valP.
move => πaπ. by rewrite myvalK can_inv -permM mulgV perm1.
Qed.


        