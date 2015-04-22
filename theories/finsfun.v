Require Import ssreflect ssrbool ssrnat eqtype choice ssrfun seq path.
Require Import fintype finfun bigop finset.
Require Import finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import Key.Exports.

Delimit Scope finsfun_scope with fsfun.
Local Open Scope finsfun_scope.
Local Open Scope fset_scope.

Section FinSFunDef.

Variables (K : keyType) (V : eqType) (default : K -> V).

Record finsfun := FinSFun {
  fmap_of_finsfun : {fmap K -> V};
  _ : [forall k : domf fmap_of_finsfun
      , fmap_of_finsfun k != default (val k)]
}.

Definition finsfun_of (_ : phant (K -> V)) := finsfun.

Canonical finsfun_subType := Eval hnf in [subType for fmap_of_finsfun].
Definition finsfun_eqMixin := [eqMixin of finsfun by <:].

Fact finsfun_subproof (f : finsfun) :
  forall (k : K) (kf : k \in fmap_of_finsfun f), (fmap_of_finsfun f).[kf]%fmap != default k.
Proof.
case:f => f f_stable k kf /=.
exact: (forallP f_stable (SeqSub kf)).
Qed.

Definition fun_of_finsfun (f : finsfun) (k : K) :=
  odflt (default k) (fmap_of_finsfun f).[? k]%fmap.

Coercion fun_of_finsfun : finsfun >-> Funclass.

Definition finsupp f := domf (fmap_of_finsfun f).

Lemma mem_finsupp f (k : K) : (k \in finsupp f) = (f k != default k).
Proof.
rewrite /fun_of_finsfun; case: fndP; rewrite ?eqxx //=.
by move=> kf; rewrite finsfun_subproof.
Qed.

Lemma finsfun_dflt f (k : K) : k \notin finsupp f -> f k = default k.
Proof. by rewrite mem_finsupp negbK => /eqP. Qed.

CoInductive finsfun_spec f (k : K) : V -> bool -> Type :=
  | FinsfunOut : k \notin finsupp f -> finsfun_spec f k (default k) false
  | FinsfunIn  (kf : k \in finsupp f) : finsfun_spec f k (f k) true.

Lemma finsuppP f (k : K) : finsfun_spec f k (f k) (k \in finsupp f).
Proof.
have [kf|kNf] := boolP (_ \in _); first by constructor.
by rewrite finsfun_dflt // ; constructor.
Qed.

Variables (h : K -> V) (S : {fset K}).
Definition suppS := FSet [set a : S | h (val a) != default (val a)].
Definition fmapS := FinMap [ffun a : suppS => h (val a)].

Fact finsfunS_subproof : [forall k : suppS, fmapS k != default (val k)].
Proof.
apply/forallP => a /=; rewrite ffunE.
by move: (ssvalP a) => /FSetP [ka /=]; rewrite in_set.
Qed.

Definition finsfun_of_fun := @FinSFun fmapS finsfunS_subproof.

Lemma finsfun_of_funE :
  (forall a : K, h a != default a -> a \in S) -> (finsfun_of_fun) =1 h.
Proof.
move => H a; symmetry; rewrite /finsfun_of_fun /fun_of_finsfun.
case: fndP => /= [kf|]; first by rewrite ffunE.
by apply:contraNeq => /(fun x => (x,x)) [/H a_in_S]; rewrite in_FSet inE.
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

Lemma finsfun_injective_inP  (f : finsfun) (T : {fset K}) :
  reflect {in T &, injective f} (injectiveb [ffun x : T => f (val x)]).
Proof.
apply: (iffP (@injectiveP _ _ _)) => f_inj a b; last first.
  by rewrite !ffunE => *; apply: val_inj; apply: f_inj => //; apply: valP.
move=> aT bT eq_ga_gb; suff: (SeqSub aT) = (SeqSub bT) by move=> [].
by apply: f_inj; rewrite !ffunE.
Qed.

End FinSFunDef.

(* à mettre au bon endroit *)
(* probablement inutile
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

*)

Section FinSFunGeneralTheory.

Variables (K : keyType) (V : eqType) (default : K -> V).
Implicit Types (f g: finsfun default).

Lemma finsfunP f g : f =1 g -> f = g.
Proof.
move=> eq_fg; apply/val_inj/fmapP => k.
have := eq_fg k; rewrite /(f _) /(g _) /=.
case: fndP; case: fndP => //= kf kg; first by move->.
  by move/eqP/negPn; rewrite finsfun_subproof.
by move/eqP/negPn; rewrite eq_sym finsfun_subproof.
Qed.

End FinSFunGeneralTheory.

Section FinSFunIdTheory.

Variables (K : keyType).
Implicit Types (f g : finsfun (@id K)).

(* Pour composer des finsfun arbitraires et avoir comp g f = g \o f *)
(* Quelles conditions faut-il supposer sur défaut ? *)
(* au moins default idempotent, peut-etre default k \in g -> k \in g *)

Definition finsfun_comp g f :=
  @finsfun_of_fun _ _ id [fun k : K => g (f k)] (finsupp f :|: finsupp g).

Notation "g * f" := (finsfun_comp g f) : finsfun_scope.

Lemma finsfunM g f : g * f =1 g \o f.
Proof.
move => k. rewrite finsfun_of_funE // => {k} k.
apply contraR. rewrite in_fsetU => /norP [kNf kNg] /=.
rewrite [f _]finsfun_dflt //. by rewrite finsfun_dflt.
Qed.

Definition emptyfun : @fset0 K -> K.
by move => x; move: (ssvalP x); rewrite in_fset0. Defined.

Definition emptyffun := finfun emptyfun.

Fact can_emptyffun : [forall k,  emptyffun k != (val k)].
Proof. by apply/forallP => k; move: (ssvalP k); rewrite in_fset0. Qed.

Definition finsfun_one := @finsfun_of_can_ffun _ _ (@id K) _ _ can_emptyffun.

Lemma finsfun1 (k : K) : finsfun_one k = k.
Proof. by case: finsuppP. Qed.

Lemma finsfun_oneP : left_id finsfun_one finsfun_comp.
Proof. by move => f; apply/finsfunP => a; rewrite finsfunM /= finsfun1. Qed.

Lemma inj_finsfun_one : injective finsfun_one.
Proof. by move => a b; rewrite !finsfun1. Qed.

Lemma finsfun_compA : associative finsfun_comp.
Proof.
move => f g h; apply/finsfunP => k.
by rewrite !finsfunM /= !finsfunM.
Qed.

Lemma inj_finsfun_comp g f : injective f -> injective g ->
                             injective (g * f).
Proof.
move => f_inj g_inj k k'. rewrite !finsfunM => gfk_eq_gfk'.
have fk_eq_fk' : f k = f k' by exact: (g_inj _ _ gfk_eq_gfk').
exact: (f_inj _ _ fk_eq_fk').
Qed.

End FinSFunIdTheory.

Section InjectiveFinSFun.

Variables (K : keyType) (V : eqType).

Let equivalent (Ps : seq Prop) :=
  if Ps is P0 :: Ps then
  let fix aux (P : Prop) (Qs : seq Prop) :=
      if Qs is Q :: Qs then (P -> Q) /\ (aux Q  Qs) else P -> P0
  in aux P0 Ps else True.

Lemma injective_finsfun_subproof (g : finsfun (@id K)) :
  equivalent [:: injective g
              ; let S := finsupp g in
                {in S &, injective g} /\ forall a : S, g (val a) \in S
              ; exists2 S : {fset K}, (finsupp g \fsubset S)
                & {in S &, injective g} /\ forall a : S, g (val a) \in S].
Proof.
split => /= [g_inj|]; last split=> [[g_inj g_st]|[S gS [g_inj g_st]] a b].
- split=> [a b ? ?|a]; first exact: g_inj.
  by rewrite mem_finsupp (inj_eq g_inj) -mem_finsupp; apply/valP.
- by exists (finsupp g)=> //; apply: fsubsetAA.
have Nfinsupp := contra (fsubsetP gS _).
wlog /andP [aS bNS] : a b / (a \in S) && (b \notin S) => [hwlog|]; last first.
  rewrite (finsfun_dflt (Nfinsupp _ bNS)) => gb_eq_a.
  by move: bNS; rewrite -gb_eq_a (g_st (SeqSub aS)).
have [[aS|aNS] [bS|bNS]] := (boolP (a \in S), boolP (b \in S)); first 3 last.
- by rewrite !finsfun_dflt // ?Nfinsupp.
- exact: g_inj.
- by apply: hwlog; rewrite aS.
by move=> gab; symmetry; apply: hwlog; rewrite // bS.
Qed.

Definition injectiveb_finsfun_id : pred (finsfun (@id K)) :=
  [pred g | (injectiveb [ffun a : finsupp g => g (val a)])
            && [forall a : finsupp g, g (val a) \in finsupp g]].

Lemma injectiveb_finsfunP (g : finsfun (@id K)) :
  reflect (injective g) (injectiveb_finsfun_id g).
Proof.
have [H1 [H2 H3]]:= injective_finsfun_subproof g.
rewrite /injectiveb_finsfun_id; apply: (iffP idP)=> [|].
  by move=> /andP [/finsfun_injective_inP ? /forallP ?]; apply/H3/H2.
by move=> /H1 [/finsfun_injective_inP ? /forallP ?]; apply/andP.
Qed.

Lemma injective_finsfunP (g : finsfun (@id K)) :
  injective g <->
  exists2 S : {fset K}, (finsupp g \fsubset S)
  & {in S &, injective g} /\ forall a : S, g (val a) \in S.
Proof. by have [H1 [H2 H3]]:= injective_finsfun_subproof g; split=> [/H1|]. Qed.

End InjectiveFinSFun.

Section Image.

Variables (K V : keyType) (default : K -> V).
Implicit Types (f : finsfun default).

Definition im f (A : {fset K}) : {fset V} :=
  fset (map f (fset_keys A)).

Lemma im_f f (A : {fset K}) (a : K) : a \in A -> f a \in im f A. 
Proof. by move => aA; rewrite in_fset; apply map_f. Qed.

Lemma mem_im f (A : {fset K}) (a : K) : 
  injective f -> (f a \in im f A) = (a \in A).
Proof.                                       
move => f_inj. apply/idP/idP; last exact: im_f.
rewrite in_fset => /mapP [x P] /eqP. by rewrite inj_eq // => /eqP ->. 
Qed.

End Image.