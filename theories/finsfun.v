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

Variables (K:keyType) (V:eqType) (default : K -> V).

Record finsfun := FinSFun {
  fmap_of_finsfun : {fmap K -> V};
  _ : [forall k:domf fmap_of_finsfun, fmap_of_finsfun k != default (val k)]
}.

Definition finsfun_of (_ : phant (K -> V)) := finsfun.

Fact finsfun_subproof (f : finsfun) : 
  forall (k : K) (kf : k \in fmap_of_finsfun f), (fmap_of_finsfun f).[kf]%fmap != default k.
Proof. case:f => f f_stable k kf /=. exact (forallP f_stable (SeqSub kf)). Qed.

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

Lemma finsfunP f (k : K) : finsfun_spec f k (f k) (k \in finsupp f).
Proof.
have [kf|kNf] := boolP (_ \in _); first by constructor.
by rewrite finsfun_dflt // ; constructor.
Qed.

Variables (h : K -> V) (S : {fset K}).
Definition suppS := FSet [set a : S | h (val a) != default (val a)].
Definition fmapS := FinMap [ffun a : suppS => h (val a)].

Fact finsfunS_subproof : [forall k : suppS, fmapS k != default (val k)].
Proof. apply/forallP => a /=. rewrite ffunE.
by move: (ssvalP a) => /in_FSetE [ka /=]; rewrite in_set.
Qed.

Definition finsfun_of_fun :=
  @FinSFun fmapS finsfunS_subproof.

Lemma finsfun_of_funE : 
  (forall a : K, h a != default a -> a \in S) -> (finsfun_of_fun) =1 h.  
Proof.
move => H a; symmetry.
rewrite/finsfun_of_fun /fun_of_finsfun /=. case: fndP => /=.
by move => kf; rewrite ffunE. 
apply:contraNeq; move=> fa_neq_dflt.
have /H a_in_S := fa_neq_dflt.
by rewrite in_FSet inE /=.
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

Lemma eq_finsfunP f g : f =1 g <-> f = g. 
Proof.
split; last by move ->.
case: f; case: g => g can_g f can_f ff_eq_fg. suff f_eq_g : f = g.
  move:f_eq_g can_g can_f ff_eq_fg -> => can_g can_f _. congr FinSFun.
  by apply bool_irrelevance.
apply/fmap_fndP=> k. case:fndP; case:fndP => //.
 - move => kg kf. congr Some. move:(ff_eq_fg k). by rewrite /fun_of_finsfun !in_fnd.
 - move => kNg kf. move : (ff_eq_fg k). rewrite/fun_of_finsfun in_fnd not_fnd //= => /eqP.
   by rewrite (negbTE (forallP can_f (SeqSub kf))).
 - move => kg kNf. move : (ff_eq_fg k). rewrite/fun_of_finsfun not_fnd //= => /eqP.
   by rewrite in_fnd /= eq_sym (negbTE (forallP can_g (SeqSub kg))).
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
Proof. by case:finsfunP. Qed.

Lemma finsfun_oneP : left_id finsfun_one finsfun_comp.
Proof. by move => f; apply/eq_finsfunP => a; rewrite finsfunM /= finsfun1. Qed. 

Lemma inj_finsfun_one : injective finsfun_one.
Proof. move => a b. by rewrite !finsfun1. Qed.

Lemma finsfun_mulP : associative finsfun_comp.
Proof. 
move => f g h. apply/eq_finsfunP => k. by rewrite !finsfunM /= !finsfunM. Qed.

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

Definition injectiveb_finsfun_id : pred (finsfun (@id K)) :=
  [pred g | (injectiveb [ffun a : finsupp g => g (val a)])
            && [forall a : finsupp g, g (val a) \in finsupp g]].

Lemma injectiveb_finsfunP (g : finsfun (@id K)) :
  reflect (injective g) (injectiveb_finsfun_id g).
Proof. 
rewrite /injectiveb_finsfun_id; apply: (iffP idP).
  move=> /andP [/finsfun_injective_inP inj_g /forallP stable_g ] a b.
  wlog /andP [ag bg] : a b / (a \in finsupp g) && (b \notin finsupp g) => [hwlog|].
    case: (finsfunP g b); case: (finsfunP g a) => //; last by move=> *; exact: inj_g.
      by move=> ag bg ga_eq_b; apply: hwlog; rewrite ?ag ?bg ?(finsfun_dflt bg).
    by move=> ag bg ga_eq_b; symmetry; apply: hwlog; rewrite ?ag ?bg ?(finsfun_dflt ag).
  rewrite (finsfun_dflt bg) => ga_eq_b; move: bg; rewrite -ga_eq_b.
  by rewrite (stable_g (SeqSub ag)).

move => g_inj; apply/andP; split.
  by apply/injectiveP => a b; rewrite !ffunE => eq_ga_gb; apply/val_inj/g_inj.
apply/forallP => a.
by rewrite mem_finsupp (inj_eq g_inj) -mem_finsupp; apply/valP.
Qed.

Lemma injective_finsfunP (g : finsfun (@id K)) :
  injective g <->
  exists2 S : {fset K}, (finsupp g \fsubset S)
  & {in S &, injective g} /\ forall a : S, g (val a) \in S.
Proof.
split => [|[S [finsupp_subset_S [g_inj_in g_stable]]]].
move => /injectiveb_finsfunP /andP [/finsfun_injective_inP g_inj_in /forallP].
  by exists (finsupp g) => //; rewrite fsubsetAA.
move=> a b.
have [[aS|aNS] [bS|bNS]] := (boolP (a \in S), boolP (b \in S)); first 3 last.
- by rewrite !finsfun_dflt // ?(contra (fsubsetP finsupp_subset_S _)).
- exact: g_inj_in.
- rewrite (finsfun_dflt (contra (fsubsetP finsupp_subset_S _) bNS)).
  by move=> ga_eq_b; move: bNS; rewrite -ga_eq_b (g_stable (SeqSub aS)).
rewrite (finsfun_dflt (contra (fsubsetP finsupp_subset_S _) aNS)).
by move=> gb_eq_a; move: aNS; rewrite gb_eq_a (g_stable (SeqSub bS)).
Qed.
  
End InjectiveFinSFun.
