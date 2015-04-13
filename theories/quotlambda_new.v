Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq.
Require Import bigop fintype finfun finset generic_quotient perm.
Require Import tuple.
Require Import fingroup.
Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition atom := nat.

Section FinPerm.

Record finPerm := FinPerm {
  perm_of :> finsfun (@id atom);
  _ : injective_finsfun_id  perm_of
}.

Lemma finperm_inj (π : finPerm) : injective π.
Proof. by case:π => *; apply/injective_finsfunP. Qed.

Lemma finsupp_stable (π : finPerm) : forall (a : atom), a \in finsupp π -> π a \in finsupp π.
Proof. 
case:π => f. rewrite /injective_finsfun_id /= => /andP [_ /forallP f_stable] a af. 
by apply (f_stable (SeqSub af)).
Qed.

Lemma surfinsupp_stable (π : finPerm) (S : {fset atom}) :
  finsupp π \fsubset S -> forall (a : atom), a \in S -> π a \in S. 
Proof.
move=> /fsubsetP S_surfinsupp a; case:finsfunP; first by []. 
by move => a_supp aS; apply/S_surfinsupp/finsupp_stable.
Qed.

Definition ffun_of_finPerm (π : finPerm) (S : {fset atom}) 
           (supp_incl_S : finsupp π \fsubset S) := 
  [ffun x:S => SeqSub (surfinsupp_stable supp_incl_S (ssvalP x))].

Lemma perm_of_finPerm_subproof (π : finPerm) (S : {fset atom}) 
      (supp_incl_S : finsupp π \fsubset S) : injectiveb (ffun_of_finPerm supp_incl_S). 
Proof.
apply/injectiveP => a b; rewrite !ffunE; move/(congr1 val) => πa_eq_πb. 
by apply/val_inj/(finperm_inj πa_eq_πb).
Qed.

Definition perm_of_finPerm π (S : {fset atom}) (supp_incl_S : finsupp π \fsubset S) := 
  Perm (perm_of_finPerm_subproof supp_incl_S).

(* ne compile pas... ?!?! *)

Lemma finPerm_of_perm_1_subproof (T:{fset atom}) (p:{perm T}) (a:atom)
 (kf: a \in T) : val ((pval p) (SeqSub kf)) \in T. 
Proof. 
 
Definition eq_perm (π π' : finPerm) :=
    [forall a:support π, π (val a) == π' (val a) :> nat]
 && [forall a: support π', π' (val a) == π (val a) :> nat].

 (* Est-ce qu'il existe un [forall] étendu aux finset,
   pour pouvoir écrire [forall a in (support π), π a == π' a]
   plutot que [forall a: support π, π (val a) == π' (val a)] ? *)

Lemma perm_inj (π : finPerm) : injective π.
Proof.
move => a1 a2.
case:permP; case:permP => {a1} {a2} a1 Ha1 a2 Ha2; first by [].
  -have : (finsfun_of (perm_of π)) {| ssval := a1; ssvalP := Ha1 |} \in support π
    by rewrite /support; apply stable.
   move => H1 H2; move : H2 H1 <- =>  H. admit.
  -have : (finsfun_of (perm_of π)) {| ssval := a2; ssvalP := Ha2 |} \in support π
    by rewrite /support; apply stable.
   move => H1 H2; move : H2 H1 <- => H. admit.   
  - move : (inj π) => /injectiveP π_inj /eqP. rewrite (inj_eq π_inj).
    by move => ?; apply/eqP.
Qed.

Definition perm_inv (π : finPerm) := FinPerm ((perm_inv (perm_of_finPerm π))).
Local Notation "p ^-1" := (perm_inv p).
