Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq.
Require Import bigop fintype finfun finset generic_quotient perm.
Require Import tuple.
Require Import fingroup.
Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition atom := nat.

Record finPerm := FinPerm {
  perm_of : finsfun (@id atom);
  inj : injectiveb (finsfun_of perm_of)
}.

Definition fun_of_perm π := fun_of_finsfun (perm_of π).

Coercion fun_of_perm : finPerm >-> Funclass.

Definition support (π : finPerm) :=
  domf (finsfun_of (perm_of π)).

(* Est-ce qu'on peut afficher par défaut a: atom plutot que
 a : Key.sort nat_KeyType ? *)


Lemma in_support π a: a \in (support π) -> π a != a.
Proof. by move => kf; rewrite/fun_of_perm /fun_of_finsfun in_fnd can. Qed.

(* Ici je donne le nom "can" à l'hypothèse qui dit que 
les finsfun sont canoniques, ou "inj" à l'hypothèse qui 
dit qu'une permutation est injective. Si je remplace
dans la définition de finPerm inj par _, comment est-ce
que j'y fais référence dans les preuves ? *) 

Lemma perm_default π a: a\notin (support π) -> π a = a.
Proof. by move => H; rewrite/fun_of_perm /fun_of_finsfun not_fnd //=. Qed.

(* Ici est-ce qu'il vaut mieux conclure π a = a ou π a == a ?
Le premier permet des rewrite, mais le deuxième est
plus précis... *) 

CoInductive perm_spec (π : finPerm) : atom -> bool -> atom -> Type :=
  | PermOut a : a \notin support π -> perm_spec π a false a
  | PermIn a  (kf: a \in support π) : perm_spec π a true (finsfun_of (perm_of π)).[kf]%fmap.

(* Les finsfun_of (perm_of ...) à rallonge, c'est pas grave ? *)

Lemma permP (π : finPerm) (a : atom) : perm_spec π a (a \in support π) (π a).
Proof.
case_eq (a \in support π) => H. 
by rewrite /fun_of_perm /fun_of_finsfun in_fnd; apply:PermIn.
  rewrite perm_default; last by apply:negbT.
  by apply PermOut; apply negbT. 
Qed.

(* J'ai jamais vu de case_eq dans les tutos ssreflect
On doit pouvoir l'éviter... ? *)

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
  move -> . (* contradictoire avec can *)
 
(* IN PROGRESS *)

Lemma in_ssupport (π : finPerm) : {mono π : a / a \in support π}.
Proof.
move => a /=. case:permP; first by move => ? /negPf.
move => {a} a H. case:fndP. done. move => H2. 
move/perm_default:(H2)=>H3. 

have: π a = a. move: (inj π).  move /injectiveP. Check perm_of π.
rewrite /injective. move:H. rewrite/support/domf.