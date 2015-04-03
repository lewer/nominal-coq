Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq.
Require Import bigop fintype finfun finset generic_quotient perm.
Require Import tuple.
Require Import fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive preterm : Type :=
| pVar of nat
| pApp of preterm & preterm
| pLambda of nat & preterm.

Fixpoint preterm_encode (t : preterm) : GenTree.tree nat :=
  match t with
    | pVar x => GenTree.Leaf x
    | pLambda x u => GenTree.Node x.+1 [:: preterm_encode u]
    | pApp u v => GenTree.Node 0 [:: preterm_encode u; preterm_encode v]
  end.

Fixpoint preterm_decode (t : GenTree.tree nat) : preterm :=
  match t with
    | GenTree.Leaf x => pVar x
    | GenTree.Node x.+1 [:: u] => pLambda x (preterm_decode u)
    | GenTree.Node 0 [:: u; v] =>
      pApp (preterm_decode u) (preterm_decode v)
    | _ => pVar 0
  end.

Lemma preterm_codeK : cancel preterm_encode preterm_decode.
Proof. by elim=> //= [? -> ? ->|? ? ->]. Qed.

Definition preterm_eqMixin := CanEqMixin preterm_codeK.
Canonical preterm_eqType := EqType preterm preterm_eqMixin.
Definition preterm_choiceMixin := CanChoiceMixin preterm_codeK.
Canonical preterm_choiceType := ChoiceType preterm preterm_choiceMixin.
Definition preterm_countMixin := CanCountMixin preterm_codeK.
Canonical preterm_countType := CountType preterm preterm_countMixin.

Fixpoint eq_var s : rel nat :=
  if s is (x0, y0) :: s then
    (fun x y => ((x == x0) && (y == y0)) ||
               (((x == x0) == (y == y0)) && eq_var s x y))
  else eq_op.

Fixpoint fun_var (s : seq (nat * nat)) (x : nat) : option nat :=
  if s is (x0, y0) :: s 
  then if x == x0 then Some y0 
       else let oy := fun_var s x in
            if oy == Some y0 then None else oy
  else Some x.
    
Definition var_inv (s : seq (nat * nat)) := [seq (x.2, x.1) | x <- s].
Lemma var_invK s : var_inv (var_inv s) = s.
Proof. by elim: s => [|[? ?] ? ihs] //=; rewrite ihs. Qed.

Require Import perm.

Require Import bigenough.
Import BigEnough.

Definition big_rel_subseq_class : big_rel_class_of (@subseq [eqType of nat]).
Proof.
exists subseq (fun ss => flatten ss) => //; first exact: subseq_trans.
  by move=> /= i s; rewrite prefix_subseq.
by move=> /= i j s /subseq_trans -> //; rewrite suffix_subseq.
Qed.
Canonical big_enough_support := BigRelOf big_rel_subseq_class.

Ltac pose_big_enough i := pose_big_enough_gen big_enough_support i.
Ltac pose_big_modulus F m := pose_big_modulus_gen big_enough_support F m.
Ltac exists_big_modulus F m := pose_big_modulus m F; first exists m.

Module PreNat.

Record perm := Perm {
  ssupport : seq nat;
  perm_of : {perm (seq_sub ssupport)}
}.

Definition perm_encode (np : perm) : {x : seq nat & {perm (seq_sub x)}} :=
  let (s, p) := np in @existT _ _ s p.
Definition perm_decode (np : {x : seq nat & {perm (seq_sub x)}}) : perm :=
  let (s, p) := np in Perm p.
  
Lemma perm_codeK : cancel perm_encode perm_decode.
Proof. by case. Qed.

Definition perm_eqMixin := CanEqMixin perm_codeK.
Canonical perm_eqType := EqType perm perm_eqMixin.
Definition perm_choiceMixin := CanChoiceMixin perm_codeK.
Canonical perm_choiceType := ChoiceType perm perm_choiceMixin.
Definition perm_countMixin := CanCountMixin perm_codeK.
Canonical perm_countType := CountType perm perm_countMixin.

Definition support p := seq_sub (ssupport p).

Definition fun_of_perm (p : perm) (n : nat) : nat :=
  if insub n : option (support p) is Some x
  then val (perm_of p x) else n.

Coercion fun_of_perm : perm >-> Funclass.

CoInductive perm_spec (p : perm) : nat -> bool -> nat -> Type :=
  | PermOut n : n \notin ssupport p -> perm_spec p n false n
  | PermIn x : perm_spec p (val x) true (val (perm_of p x)).

Lemma permP (p : perm) (n : nat) : perm_spec p n (n \in ssupport p) (p n).
Proof.
rewrite /(p _); case: insubP => //=; first by move=> u -> /= <-; constructor.
by move=> Hn; rewrite (negPf Hn); constructor.
Qed.

Definition eq_perm (p p' : perm) :=
    [forall x : support p, p (val x) == p' (val x) :> nat]
 && [forall x : support p', p' (val x) == p (val x) :> nat].

Lemma perm_default n p : n \notin ssupport p -> p n = n.
Proof. by case: permP. Qed.

Lemma perm_val p (n : support p) : p (val n) = val (perm_of p n).
Proof. by rewrite /(p _) valK. Qed.

Lemma perm_eval p n (Hn : n \in ssupport p) : p n = val (perm_of p (SeqSub Hn)).
Proof. by rewrite -perm_val. Qed.

Lemma eq_permP (p p' : perm) : reflect (p =1 p') (eq_perm p p').
Proof.
apply: (iffP idP); last first.
  by move=> pp'; apply/andP; split; apply/forallP => x; rewrite pp'.
move=> /andP [/forallP /= pp' /forallP /= p'p] n.
case: permP => {n} [n|n]; last by rewrite -perm_val (eqP (pp' _)).
by case: permP => {n} n //= Hn; rewrite -perm_val (eqP (p'p _)) perm_default.
Qed.
  
Lemma eq_perm_is_equiv : equiv_class_of eq_perm.
Proof.
split=> [p|p q|q p r].
  by rewrite /eq_perm andbb; apply/forallP.
  by rewrite /eq_perm andbC.
move=> /eq_permP pq /eq_permP qr.
by apply/eq_permP => n; rewrite pq qr.
Qed.

Canonical eq_perm_equiv := EquivRelPack eq_perm_is_equiv.

Lemma in_ssupport (p : perm) : {mono p : n / n \in ssupport p}.
Proof. by move=> n /=; case: permP => [? /negPf-> //|x]; rewrite ssvalP. Qed.

Definition perm_inv (p : perm) := Perm ((perm_of p)^-1)%g.
Local Notation "p ^-1" := (perm_inv p).

Lemma perm_invK : involutive perm_inv.
Proof. by case => s p; rewrite /perm_inv /= invgK. Qed.

Lemma permK (p : perm) : cancel p p^-1.
Proof.
move=> n /=; case: (permP p) => {n} [n Hn|n]; first by rewrite perm_default.
by rewrite /= perm_val /= -permM mulgV perm1.
Qed.

Lemma permVK (p : perm) : cancel p^-1 p.
Proof. by move=> n; rewrite -{1}[p]perm_invK permK. Qed.

Lemma perm_for_subproof (p : perm) :
  forall s, subseq (ssupport p) s -> {p' : {perm seq_sub s} | p =1 Perm p'}.
Proof.
move=> s Hs.
have p'P (x : seq_sub s) : p (val x) \in s.
  case: permP (ssvalP x) => // {x} x _.
  by rewrite (mem_subseq Hs) //= ssvalP.
have p'_inj: injective (fun x => SeqSub (p'P x)).
  by move=> x y /= [] /(can_inj (permK _)) ?; apply: val_inj.
exists (perm.perm p'_inj).
move=> n /=; case: permP => /= {n} n.
  by case: permP => {n} n //= Hn; rewrite permE /= perm_default.
have ns : val n \in s by rewrite (mem_subseq Hs) ?ssvalP.
by rewrite perm_eval /= permE /= perm_val.
Qed.

Definition perm_for s p : {perm (seq_sub s)} := 
  if subseq (ssupport p) s =P true is ReflectT P
  then projT1 (perm_for_subproof P) else 1%g.

Lemma permE_for s (p : perm) :
  subseq (ssupport p) s -> p =1 Perm (perm_for s p).
Proof.
by rewrite /perm_for; case: eqP => //= Hs _ n; case: perm_for_subproof.
Qed.

Definition perm_mul p q :=
  let s := ssupport p ++ ssupport q in
  let p := perm_for s p in let q := perm_for s q in
  Perm (p * q)%g.
Local Notation "p * q" := (perm_mul p q).

Lemma permM (p q : perm) n : (p * q) n = q (p n).
Proof.
rewrite /perm_mul; set s := _ ++ _; case: permP => //= {n} n.
  by rewrite mem_cat => /norP [np nq]; rewrite !perm_default.
rewrite permM /= (@permE_for s q) /= ?suffix_subseq //.
by rewrite (@permE_for s p) /= ?prefix_subseq // !perm_val.
Qed.

End PreNat.

Local Open Scope quotient_scope.

Canonical PreNat.perm_eqType.
Canonical PreNat.perm_countType.
Canonical PreNat.perm_choiceType.
Canonical PreNat.eq_perm_equiv.

Coercion PreNat.fun_of_perm : PreNat.perm >-> Funclass.

Definition natperm := {eq_quot PreNat.eq_perm}.
(* Canonical term_subType := [subType of term by %/]. *)
Definition natperm_eqMixin := [eqMixin of natperm].
Canonical natperm_eqType := EqType natperm natperm_eqMixin.
Canonical natperm_choiceType := Eval hnf in [choiceType of natperm].
Canonical natperm_countType := Eval hnf in [countType of natperm].
Canonical natperm_quotType := Eval hnf in [quotType of natperm].
Canonical natperm_eqQuotType :=
  Eval hnf in [eqQuotType PreNat.eq_perm of natperm].

Lemma eq_natpermE x y : PreNat.eq_perm x y = (x == y %[mod natperm]).
Proof. by rewrite piE. Qed.

Delimit Scope natperm_scope with p.

Section NatPermTheory.

Definition fun_of_natperm := lift_fun1 natperm PreNat.fun_of_perm.
Local Coercion fun_of_natperm : natperm >-> Funclass.

Lemma fun_of_natperm_subproof (pp : PreNat.perm) (p : {pi pp}) (n : nat) : 
    pp n = (equal_val p : natperm) n.
Proof.
unlock fun_of_natperm; case: p => p /=.
by rewrite -{1}[p]reprK => /eqmodP /PreNat.eq_permP ->.
Qed.

Canonical pi_fun_of_natperm
  (pp : PreNat.perm) (p : {pi pp}) (n : nat) : equal_to (pp n) :=
  EqualTo (fun_of_natperm_subproof p n).

Import generic_quotient.

Lemma repr_perm (p : natperm) : repr p =1 p.
Proof.
elim/quotW: p => p /= n; rewrite !piE; move: n.
by apply/PreNat.eq_permP; rewrite eq_natpermE reprK.
Qed.

Definition natperm_mul := lift_op2 natperm PreNat.perm_mul.

Lemma pi_natperm_mul :
  {morph \pi_natperm : p q / PreNat.perm_mul p q >-> natperm_mul p q}.
Proof.
move=> p q /=; unlock natperm_mul.
apply/eqmodP/PreNat.eq_permP => n /=.
by rewrite !PreNat.permM /= !repr_perm !piE.
Qed.
Canonical natperm_mul_morphism := PiMorph2 pi_natperm_mul.

Notation "p * q" := (natperm_mul p q) : natperm_scope.

Definition NatPerm (s : seq nat) : 
  {perm (seq_sub s)} -> natperm := lift_embed natperm (@PreNat.Perm s).
Canonical NatPerm_morph s := PiEmbed (@NatPerm s).

Definition natperm_one := @NatPerm [::] 1%g.
Notation "1" := natperm_one : natperm_scope.

Definition tnatperm x y :=
  @NatPerm [::x; y] (tperm (SeqSub (mem_head _ _))
                           (SeqSub (mem_last _ _))).

Definition natperm_inv := lift_op1 natperm PreNat.perm_inv.

Lemma pi_natperm_inv :
  {morph \pi_natperm : p / PreNat.perm_inv p >-> natperm_inv p}.
Proof.
move=> p /=; unlock natperm_inv; set p' := repr _.
apply/eqmodP/PreNat.eq_permP=> /= n; apply: (canLR (PreNat.permK p)).
have -> : p =1 p' by apply/PreNat.eq_permP; rewrite eq_natpermE reprK.
by rewrite PreNat.permVK.
Qed.
Canonical natperm_inv_morphism := PiMorph1 pi_natperm_inv.

(* Lemma mulpA : associative natperm_mul. *)
(* Proof. *)
(* elim/quotW => p; elim/quotW => q; elim/quotW => r; rewrite !piE. *)
(* apply/eqmodP/PreNat.eq_permP => n /=. *)

End NatPermTheory.

Notation "1" := natperm_one : natperm_scope.
Notation "p * q" := (natperm_mul p q) : natperm_scope.
Notation "p ^-1" := (natperm_inv p) : natperm_scope.

Module Nominal.

Record mixin_of (T : Type) := Mixin {
  act : natperm -> T -> T;
  nsupport : T -> seq nat;
  _ : act 1%p =1 id;
  _ : forall p q x, act (p * q)%p x = act q (act p x);
  _ : forall (p : natperm) (x : T), 
        (forall n, n \in nsupport x -> fun_of_natperm p n = n) -> act p x = x
}.

Record type := Pack {sort :> Type; class : mixin_of sort; _ : Type}.

End Nominal.

Notation nominalType := Nominal.type.
Coercion Nominal.sort : nominalType >-> Sortclass.

Section NominalNat.

Local Notation natact := fun_of_natperm.

Lemma natact1 : natact 1%p =1 id.
Proof. by move=> n; rewrite piE PreNat.perm_default. Qed.

Lemma natactM p q x : natact (p * q)%p x = natact q (natact p x).
Proof. by elim/quotW: p; elim/quotW: q => p q; rewrite !piE PreNat.permM. Qed.

Lemma natact_id (p : natperm) (x : nat) :
     (forall n, n \in [::x] -> natact p n = n) -> natact p x = x.
Proof. by apply; rewrite mem_head. Qed.

Definition nat_nominal_mixin := Nominal.Mixin natact1 natactM natact_id.
Canonical nat_nominalType := @Nominal.Pack nat nat_nominal_mixin nat.

End NominalNat.

Section NominalTheory.

Implicit Type T : nominalType.

Definition act p {T} := Nominal.act (Nominal.class T) p.
(* Coercion act : natperm >-> Funclass. *)

Canonical pi_act
  (pp : PreNat.perm) (p : {pi pp}) (n : nat) : equal_to (pp n) :=
  @EqualTo _ _ (act _ _) (fun_of_natperm_subproof p n).

Lemma natpermP (p q : natperm) : act p =1 act q :> nat -> nat <-> p = q.
Proof.
split; last by move->.
elim/quotW: p => p; elim/quotW: q => q pq.
by apply/eqmodP/PreNat.eq_permP => n; have := pq n; rewrite !piE.
Qed.

Definition nsupport T := Nominal.nsupport (Nominal.class T).

Lemma natperm_for_subproof (p : natperm) :
  {s' : _ & forall s, subseq s' s -> {p' : {perm seq_sub s} | p = NatPerm p'}}.
Proof.
elim/quotW: p => p; pose_big_enough s'.
  exists s' => s Hs; exists (PreNat.perm_for s p).
  by apply/natpermP => n; rewrite !piE /= -PreNat.permE_for.
by close.
Qed.

Definition support_perm_for p := projT1 (natperm_for_subproof p).

Definition perm_for s p : {perm (seq_sub s)} := 
  if subseq (support_perm_for p) s =P true is ReflectT P
  then projT1 ((projT2 (natperm_for_subproof p)) _ P) else 1%g.

Lemma perm_forK s (p : natperm) : subseq (support_perm_for p) s ->
  NatPerm (perm_for s p) = p.
Proof.
rewrite /perm_for /support_perm_for; case: eqP => //=.
by case: natperm_for_subproof => //= ? /(_ s) /= H xs _; case: H.
Qed.

Lemma NatPerm_inj s : injective (@NatPerm s).
Proof.
move=> x y /natpermP xy; apply: val_inj; apply/ffunP => n /=; apply: val_inj.
by move: (xy (val n)); rewrite !piE !PreNat.perm_val /=! pvalE.
Qed.
 
Lemma NatPermK s (p : {perm seq_sub s}) :
  subseq (support_perm_for (NatPerm p)) s ->
  (* not needed with a good notion of smallest support *)
  perm_for s (NatPerm p) = p.
Proof. by move=> Hs; apply: NatPerm_inj; rewrite perm_forK. Qed.

Lemma NatPermM s : {morph @NatPerm s : p q / (p * q)%g >-> (p * q)%p}.
Proof.
move=> p q /=; apply/natpermP => n; rewrite !piE /= PreNat.permM.
case: PreNat.permP => //= {n} [n Hn|n].
  by rewrite !PreNat.perm_default.
by rewrite !PreNat.perm_val /= permM.
Qed.

Lemma NatPermV s : {morph @NatPerm s : p / (p^-1)%g >-> (p^-1)%p}.
Proof. by move=> p /=; apply/natpermP => n; rewrite !piE. Qed.

Lemma perm_forM_subproof p q : {bigs | forall s, subseq bigs s -> 
  perm_for s (p * q)%p = (perm_for s p * perm_for s q)%g}.
Proof.
pose_big_enough bigs.
  by exists bigs => s Hs; apply: NatPerm_inj; rewrite NatPermM !perm_forK.
by close.
Qed.

Definition support_perm_forM p q := projT1 (perm_forM_subproof p q).
Lemma perm_forM p q s : subseq (support_perm_forM p q) s ->
  perm_for s (p * q)%p = (perm_for s p * perm_for s q)%g.
Proof. by rewrite /support_perm_forM; case: perm_forM_subproof=> ?; apply. Qed.

Lemma perm_forV_subproof p : {bigs | forall s, subseq bigs s -> 
  perm_for s (p^-1)%p = (perm_for s p)^-1%g}.
Proof.
pose_big_enough bigs.
  by exists bigs => s Hs; apply: NatPerm_inj; rewrite NatPermV !perm_forK.
by close.
Qed.

Definition support_perm_forV p := projT1 (perm_forV_subproof p).
Lemma perm_forV p s : subseq (support_perm_forV p) s ->
  perm_for s (p^-1)%p = (perm_for s p)^-1%g.
Proof. by rewrite /support_perm_forV; case: perm_forV_subproof=> ?; apply. Qed.

Lemma act1 T : @act 1%p T =1 id.
Proof. by case: T => ? []. Qed.

Lemma actM T p q (x : T) : act (p * q)%p x = act q (act p x).
Proof. by case: T p q x => ? []. Qed.

Lemma act_id T (p : natperm) (x : T) :
  (forall n, n \in nsupport x -> act p n = n) -> act p x = x.
Proof. by case: T p x => ? []. Qed.

Lemma NatPerm1 s : @NatPerm s 1 = 1%p.
Proof.
apply/natpermP => n; rewrite !piE [RHS]PreNat.perm_default //.
by case: PreNat.permP => //= {n} n /=; rewrite perm1.
Qed.

Lemma mulpV p : (p * p^-1)%p = 1%p.
Proof.
pose_big_enough s.
  by rewrite -[p](@perm_forK s) // -NatPermV -NatPermM mulgV NatPerm1.
by close.
Qed.

Lemma mulVp p : (p^-1 * p)%p = 1%p.
Proof.
pose_big_enough s.
  by rewrite -[p](@perm_forK s) // -NatPermV -NatPermM mulVg NatPerm1.
by close.
Qed.

Lemma mulpA : associative natperm_mul.
Proof. by move=> p q r; apply/natpermP => n; rewrite !actM. Qed.

Lemma mul1p : left_id 1%p natperm_mul.
Proof. by move=> p; apply/natpermP => n; rewrite actM act1. Qed.

Lemma mulp1 : right_id 1%p natperm_mul.
Proof. by move=> p; apply/natpermP => n; rewrite actM act1. Qed.

Lemma actK T p : cancel (@act p T) (@act p^-1%p T).
Proof. by move=> x; rewrite -actM mulpV act1. Qed.

Lemma actVK T p : cancel (@act p^-1%p T) (@act p T).
Proof. by move=> x; rewrite -actM mulVp act1. Qed.

Lemma act_tnatperm x y : act (tnatperm x y) =1 [fun z => z with x |-> y, y |-> x].
Proof.
move=> z; rewrite /tnatperm piE //=.
case: PreNat.permP => //= n.
  by rewrite !in_cons in_nil orbF => /norP [/negPf-> /negPf->].
case: tpermP => //=; do ? by move=> -> /=; do 2?case: eqP.
by do 2! [move=> /eqP; rewrite -val_eqE /= => /negPf ->].
Qed.

Lemma tnatpermL x y : act (tnatperm x y) x = y.
Proof. by rewrite act_tnatperm /= eqxx. Qed.

Lemma tnatpermR x y : act (tnatperm x y) y = x.
Proof. by rewrite act_tnatperm /= eqxx; case: eqP. Qed.

Lemma tnatpermD x y z : x != z -> y != z -> act (tnatperm x y) z = z.
Proof. by rewrite act_tnatperm /= ![_ == z]eq_sym => /negPf-> /negPf->. Qed.

Definition new (P : nat -> Prop) :=
  exists s : seq nat, forall n, n \notin s -> P n.

Notation "\new x , P" := (new (fun x => P))
   (format "\new  x ,  P", at level 200).

Definition big_fresh x v : \max_(y <- v) y < x -> x \in v = false.
Proof.
elim: v=> [|y v ihv] //=; rewrite big_cons /= -maxnSS geq_max in_cons.
by move=> /andP [yx x_big]; rewrite gtn_eqF //= ihv.
Qed.

Definition fresh v := (\max_(x <- v) x).+1.

Lemma fresh_notin v : fresh v \notin v.
Proof. by rewrite big_fresh. Qed.

Hint Resolve fresh_notin.

Lemma fresh_in (v s : seq nat) : {subset s <= v} -> fresh v \in s = false.
Proof.
move=> sv; have: fresh v \notin v by [].
by apply: contraNF; apply: sv.
Qed.

Notation nfresh x := (fresh (nsupport x)).

Theorem some_any T (R : nat -> T -> Prop) :
  (forall (p : natperm) n x, R (act p n) (act p x) <-> R n x) ->
  forall x : T, [/\
      (forall n, n \notin nsupport x -> R n x) -> (\new n, R n x),
      (\new n, R n x) ->  R (nfresh x) x,
      R (nfresh x) x -> (exists2 n, n \notin nsupport x & R n x) &
      (exists2 n, n \notin nsupport x & R n x)
      -> (forall n, n \notin nsupport x -> R n x)
    ].
Proof.
move=> Requi x; split; first by move=> Rnx; exists (nsupport x).
  case=> s Rnx; pose_big_enough_gen leq n.
    apply/(Requi (tnatperm (nfresh x) n)).
    rewrite tnatpermL act_id; first by apply: Rnx; rewrite big_fresh.
    move=> m mx; rewrite tnatpermD //; apply: contraTN mx => /eqP<- //.
    by rewrite big_fresh.
  by close.
  by exists (nfresh x).
move=> [n nx] Rnx m mx; apply/(Requi (tnatperm n m)).
rewrite tnatpermR act_id // => a ax; rewrite tnatpermD //.
  by apply: contra nx => /eqP->.
by apply: contra mx => /eqP->.
Qed.

Lemma new_forall T (R : nat -> T -> Prop) :
  (forall (p : natperm) n x, R (act p n) (act p x) <-> R n x) ->
  forall x : T, ((\new n, R n x) <-> (forall n, n \notin nsupport x -> R n x)).
Proof.
by move=> H x; have [? nh he ?] := some_any H x; split=> // /nh /he.
Qed.

Lemma new_fresh T (R : nat -> T -> Prop) :
  (forall (p : natperm) n x, R (act p n) (act p x) <-> R n x) ->
  forall x : T, ((\new n, R n x) <-> (R (nfresh x) x)).
Proof.
by move=> H x; have [? ? he ef] := some_any H x; split=> // /he /ef.
Qed.

Lemma new_exists  T (R : nat -> T -> Prop) :
  (forall (p : natperm) n x, R (act p n) (act p x) <-> R n x) ->
  forall x : T, ((\new n, R n x) <-> (exists2 n, n \notin nsupport x & R n x)).
Proof.
by move=> H x; have [fn nh he ef] := some_any H x; split=> [/nh|/ef].
Qed.

Fixpoint termact (p : natperm) t :=
  match t with
    | pVar x => pVar (act p x)
    | pApp u v => pApp (termact p u) (termact p v)
    | pLambda x t => pLambda (act p x) (termact p t)
  end.

Fixpoint term_support (t : preterm) : seq nat :=
  match t with
    | pVar x => [:: x]
    | pApp u v => undup (term_support u ++ term_support v)
    | pLambda x u => undup (x :: term_support u)
  end.

Fixpoint pre_fv (t : preterm) : seq nat :=
  match t with
    | pVar x => [:: x]
    | pApp u v => undup (pre_fv u ++ pre_fv v)
    | pLambda x u => [seq y <- pre_fv u | y != x]
  end.

Section NominalTerm.

Lemma termact1 : termact 1%p =1 id.
Proof. by elim => [n|u ihu v ihv|n u ihu]; rewrite /= ?act1 ?ihu ?ihv. Qed.

Lemma termactM p q x : termact (p * q)%p x = termact q (termact p x).
Proof. by elim: x => [n|u ihu v ihv|n u ihu] /=; rewrite ?actM ?ihu ?ihv. Qed.

Lemma termact_id (p : natperm) (x : preterm) :
     (forall n : nat, n \in term_support x -> act p n = n) -> termact p x = x.
Proof.
elim: x => [n|u ihu v ihv|n u ihu] /= Hp.
  by rewrite act_id.
  by rewrite ?ihu ?ihv // => n nuv; rewrite ?Hp // mem_undup mem_cat nuv ?orbT.
rewrite ?ihu ?Hp //.
  by case: ifP=> H; rewrite ?mem_head // mem_undup.
move=> m mu; rewrite Hp //.
by case: ifP=> H; rewrite ?in_cons ?mem_undup ?mu ?orbT.
Qed.

Definition term_nominal_mixin := Nominal.Mixin termact1 termactM termact_id.
Canonical term_nominalType := @Nominal.Pack preterm term_nominal_mixin preterm.

End NominalTerm.

Section NominalProd.

Variables X Y : nominalType.

Definition prodact (p : natperm) (x : X * Y) := (act p x.1, act p x.2).

Lemma prodact1 : prodact 1%p =1 id.
Proof. by case=> x y; rewrite /prodact /= !act1. Qed.

Lemma prodactM p q x : prodact (p * q)%p x = prodact q (prodact p x).
Proof. by case: x => x y; rewrite /prodact /= !actM. Qed.

Lemma prodact_id (p : natperm)  (x : X * Y) :
     (forall n : nat, n \in undup (nsupport x.1 ++ nsupport x.2) -> act p n = n)
     -> prodact p x = x.
Proof.
case: x => x y /= Hp; rewrite /prodact /=.
by rewrite !act_id // => n Hn; rewrite Hp // mem_undup mem_cat Hn ?orbT.
Qed.

Definition prod_nominal_mixin := Nominal.Mixin prodact1 prodactM prodact_id.
Canonical prod_nominalType := @Nominal.Pack (X * Y) prod_nominal_mixin (X * Y).

End NominalProd.

Section NominalSeq.

Variables X : nominalType.

Definition seqact (p : natperm) (s : seq X) := [seq act p x | x <- s].

Lemma seqact1 : seqact 1%p =1 id.
Proof. by move=> x; rewrite /seqact /= (eq_map (@act1 _)) map_id. Qed.

Lemma seqactM p q s : seqact (p * q)%p s = seqact q (seqact p s).
Proof. by rewrite /seqact (eq_map (actM _ _)) map_comp. Qed.

Lemma seqact_id (p : natperm) (s : seq X) :
  (forall n : nat, n \in undup (flatten [seq nsupport x | x <- s])
                         -> act p n = n)
     -> seqact p s = s.
Proof.
elim: s => //= x s ihx Hp.
rewrite ihx ?act_id // => n; rewrite ?mem_undup => Hn.
  by rewrite Hp // mem_undup mem_cat ?Hn //.
by rewrite Hp // mem_undup mem_cat ?Hn // orbT.
Qed.

Definition seq_nominal_mixin := Nominal.Mixin seqact1 seqactM seqact_id.
Canonical seq_nominalType := @Nominal.Pack (seq X) seq_nominal_mixin (seq X).

End NominalSeq.

Fixpoint pre_depth (t : preterm) : nat :=
  match t with 
    | pVar _ => 0
    | pApp u v => (maxn (pre_depth u) (pre_depth v)).+1
    | pLambda _ u => (pre_depth u).+1
  end.

Lemma pre_depth_perm (p : natperm) t : pre_depth (act p t) = pre_depth t.
Proof. by elim: t => [x|u ihu v ihv|x u ihu] //=; rewrite ?ihu ?ihv. Qed.

Fixpoint alpha_rec n t t' :=
  match n, t, t' with
    | n, pVar x, pVar y => x == y
    | S n, pLambda x u, pLambda y u' =>  let z := nfresh ((x ,y), (u, u')) in 
                    alpha_rec n (act (tnatperm x z) u) (act (tnatperm y z) u')
    | S n, pApp u v, pApp u' v' => alpha_rec n u u' && alpha_rec n v v'
    | _, _, _ => false
  end.
Definition alpha t t' := alpha_rec (pre_depth t) t t'.

Lemma alpha_recE n t t' : (pre_depth t <= n) -> alpha_rec n t t' = alpha t t'.
Proof.
rewrite /alpha; move: {-2}n (leqnn n).
elim: n t t' => //= [|n ihn] [x|u v|x u] [y|u' v'|y u'] [|m] //=.
  rewrite !ltnS geq_max => lmn /andP [um vm]. 
  by rewrite !ihn // ?(leq_maxl, leq_maxr) ?geq_max
             ?(leq_trans um, leq_trans vm).
by rewrite !ltnS => lmn um; rewrite ihn // ?pre_depth_perm //.
Qed.

Inductive alpha_spec : preterm -> preterm -> Prop := 
  | AlphaVar x : alpha_spec (pVar x) (pVar x)
  | AlphaApp u v u' v' :
      alpha_spec u u' -> alpha_spec v v' -> alpha_spec (pApp u v) (pApp u' v')
  | AlphaLambda x y u u' : 
      (\new z, alpha_spec (act (tnatperm x z) u) (act (tnatperm y z) u')) -> 
      alpha_spec (pLambda x u) (pLambda y u').

Lemma alpha_ind (P : preterm -> preterm -> Prop) :
(forall x : nat, P (pVar x) (pVar x)) ->
(forall u v u' v' : preterm, alpha_spec u u' -> P u u' ->
                             alpha_spec v v' -> P v v' -> 
                             P (pApp u v) (pApp u' v')) ->
(forall (x y : nat) (u u' : term_nominalType),
 (\new z, alpha_spec (act (tnatperm x z) u) (act (tnatperm y z) u')) ->
 (\new z, P (act (tnatperm x z) u) (act (tnatperm y z) u')) ->
 P (pLambda x u) (pLambda y u')) ->
forall t t' : preterm, alpha_spec t t' -> P t t'.
Proof.
move=> Pvar Papp Plam t t'.
move: {-1}(pre_depth t) (leqnn (pre_depth t)) => n.
elim: n t t' => [|n ihn] t t'.
  by rewrite leqn0 => /eqP dt att'; case: att' dt.
rewrite leq_eqVlt => /predU1P [dt att'|/ihn]; last exact.
case: att' dt => //.
  move=> u v u' v' auu' avv' /= [duv].
  by apply: Papp => //; apply: ihn => //; rewrite -duv (leq_maxl, leq_maxr).
move=> x y u u' auu' [du]; apply: Plam => //.
case: auu' => s Hs; exists s => m ms.
by apply: ihn; rewrite ?pre_depth_perm ?du //; apply: Hs.
Qed.

Lemma act_NatPerm s p n (Hn : n \in s) :
  act (@NatPerm s p) n = val (p (SeqSub Hn)).
Proof. by rewrite !piE PreNat.perm_eval. Qed.

Lemma big_support (x : nat) s : subseq [::x] s -> x \in s.
Proof. by rewrite sub1seq. Qed.

Lemma tnatpermE s x y (xs : x \in s) (ys : y \in s) :
  tnatperm x y = NatPerm (tperm (SeqSub xs) (SeqSub ys)).
Proof.
apply/natpermP=> n; rewrite act_tnatperm piE /=.
case: PreNat.permP => /= {n} n.
  by do ?[case: ifP; first by move/eqP->; rewrite ?xs ?ys //].
by rewrite permE /= ![ssval (if _ then _ else _)]fun_if -!val_eqE /=.
Qed.

Lemma val_perm_for s p x : subseq (support_perm_for p) s ->
                           val ((perm_for s p) x) = act p (val x).
Proof.
move=> bigs; rewrite -[p in RHS](@perm_forK s) //= act_NatPerm ?ssvalP //.
by move=> Hs /=; congr (val ((perm_for _ _) _)); apply: val_inj.
Qed.

Lemma actnatE s p x (xs : x \in s) : subseq (support_perm_for p) s -> 
            act p x = val ((perm_for s p) (SeqSub xs)).
Proof. by move=> Hs; rewrite val_perm_for. Qed.

Lemma tnatperm_act p x y :
  (tnatperm (act p x) (act p y)) = (p^-1 * (tnatperm x y) * p)%p.
Proof.
pose_big_enough s.
  rewrite -[p in RHS](@perm_forK s) //=.
  rewrite (@tnatpermE s x y) ?big_support //= => xs ys.
  rewrite -NatPermV -!NatPermM -mulgA -conjgE tpermJ.
  rewrite (@tnatpermE s) ?big_support // => pxs pys.
  by congr (NatPerm (tperm _ _)); apply: val_inj; rewrite val_perm_for.
by close.
Qed.

Lemma equi_alpha_spec p u v : alpha_spec (act p u) (act p v) <-> alpha_spec u v.
Proof.
wlog suff : p u v / alpha_spec u v -> alpha_spec (act p u) (act p v) => [hw|].
  split; last exact: hw.
  by move=> /(hw p^-1%p); rewrite !actK.
move=> /alpha_ind E; elim/E : {u v E} _ =>
  [x|u v u' v' uu' auu' vv' avv'|x y u u' Hu Hpu]. 
  by constructor.
 rewrite /act /= -![termact _]/(@act _ term_nominalType).
 by constructor.
case: Hpu => s Hs.
rewrite /act /= -![termact _]/(@act _ term_nominalType).
constructor; exists (act p s) => n Hn.
rewrite -[n](actVK p) !tnatperm_act -!actM !mulpA !mulpV !mul1p !actM.
by apply: Hs; rewrite -(mem_map (can_inj (@actK nat_nominalType p))) actVK.
Qed.

Lemma equi_alpha p : {mono act p : u v / alpha u v}.
Proof.
move=> u v /=; rewrite /alpha pre_depth_perm.
move: {-1}(pre_depth u) (leqnn (pre_depth u)) => n.
elim: n u v => [|n ihn] [x|u v|x u] [y|u' v'|y u'] //=;
  do ?by rewrite (inj_eq (can_inj (@actK nat_nominalType p))) //.
  by rewrite ltnS geq_max => /andP [un vn]; rewrite !ihn.
rewrite ltnS => un.
pose P z x := alpha_rec n
     (act (tnatperm x.1.1 z) x.2.1) (act (tnatperm x.1.2 z) x.2.2).
(* set z := nfresh _f. *)
(* transitivity (P z (act p x, act p y, (act p u, act p u'))). *)
(*   done. *)



(* rewrite -[n](actVK p) !tnatperm_act -!actM !mulpA !mulpV !mul1p !actM. *)

(*   rewrite !alpha_recE. *)

(* wlog suff : p u v / alpha_spec u v -> alpha_spec (act p u) (act p v) => [hw|]. *)
(*   split; last exact: hw. *)
(*   by move=> /(hw p^-1%p); rewrite !actK. *)
(* move=> /alpha_ind E; elim/E : {u v E} _ => *)
(*   [x|u v u' v' uu' auu' vv' avv'|x y u u' Hu Hpu]. *)
(*   by constructor. *)
(*  rewrite /act /= -![termact _]/(@act _ term_nominalType). *)
(*  by constructor. *)
(* case: Hpu => s Hs. *)
(* rewrite /act /= -![termact _]/(@act _ term_nominalType). *)
(* constructor; exists (act p s) => n Hn. *)
(* rewrite -[n](actVK p) !tnatperm_act -!actM !mulpA !mulpV !mul1p !actM. *)
(* by apply: Hs; rewrite -(mem_map (can_inj (@actK nat_nominalType p))) actVK. *)
Admitted.

Lemma alphaP t t' : reflect (alpha_spec t t') (alpha t t').
Proof.
pose P z x := alpha_spec
     (act (tnatperm x.1.1 z) x.2.1) (act (tnatperm x.1.2 z) x.2.2).
have equiP p z x : P (act p z) (act p x) <-> P z x.
  case: x => [[m n] [u v]]; rewrite /P /=.
  by rewrite !tnatperm_act -!actM !mulpA !mulpV !mul1p !actM equi_alpha_spec.
apply: (iffP idP).
  rewrite /alpha.
  move: {-1}(pre_depth t) (leqnn (pre_depth t)) => n.
  elim: n t t' => [|n ihn] [x|u v|x u] [y|u' v'|y u'] //=.
    by move=> _ /eqP->; constructor.
    by move=> _ /eqP->; constructor.
    rewrite ?ltnS geq_max => /andP [nu vn]  /andP [Hu Hv].
    by constructor; apply: ihn.
  rewrite ltnS => un Hu; constructor.
  suff: \new z, P z ((x, y), (u, u')) by [].
  by apply/new_fresh => //; apply: ihn => //=; rewrite pre_depth_perm.
move => /alpha_ind E; elim/E: {t t' E}_ => //=.
  by move=> x; rewrite /alpha  /=.
  move=> u v u' v' asuu' auu' asvv' avv'.
  by rewrite /alpha /= !alpha_recE ?(leq_maxl, leq_maxr) // ?auu' ?avv'.
move=> x y u v asuv auv; rewrite /alpha /= !alpha_recE ?pre_depth_perm //.
suff: \new z, P z ((x, y), (u, v)).
  move/(new_fresh equiP); rewrite /P /=.
   have := (new_fresh _ x).

  (* exists (nsupport (u, u')) => m Hm. *)
  (* apply: ihn. *)

 
  (* rewrite alpha_recE ?pre_depth_perm // => Hu; constructor. *)
  (* exists (nsupport (u, u')) => n hn. *)
  (* apply: ihu. *)
  (* pose P z x := alpha_spec (tnatperm x.1.1 z _ x.2.1) (tnatperm x.1.2 z _ x.2.2). *)
  (* suff: \new z, P z ((x, y), (u, u')) by []. *)
  (* apply/new_exists; last first. *)
  (*   exist *)
   
  
      

(* rewrite /alpha. *)
(* elim: t t' => [x|u ihu v ihv|x u ihu] [y|u' v'|y u'] //=. *)
Admitted.

Lemma alpha_depth t t' : alpha t t' -> pre_depth t = pre_depth t'.
Proof.
(* elim: t t' s => [x|u ihu v ihv|x u ihu] [y|u' v'|y u'] f //=. *)
(*   by move=> /andP [/ihu-> /ihv->]. *)
(* by move=> /ihu->. *)
(* Qed. *)
Admitted.

Local Open Scope quotient_scope.

(* Definition pperm_encode (p : pperm) : seq nat * seq nat := *)
(*   let (s, n) := p in (s, n). *)
(* Definition pperm_decode (p : seq (nat * nat) * seq nat) : pperm := *)
(*   let (s, n) := p in PartialPerm s n. *)
(* Lemma pperm_codeK : cancel pperm_encode pperm_decode. *)
(* Proof. by case. Qed. *)

(* Definition pperm_eqMixin := CanEqMixin pperm_codeK. *)
(* Canonical pperm_eqType := EqType pperm pperm_eqMixin. *)
(* Definition pperm_choiceMixin := CanChoiceMixin pperm_codeK. *)
(* Canonical pperm_choiceType := ChoiceType pperm pperm_choiceMixin. *)
(* Definition pperm_countMixin := CanCountMixin pperm_codeK. *)
(* Canonical pperm_countType := CountType pperm pperm_countMixin. *)

(* Fixpoint fun_of_pperm (p :pperm) (x : nat) : option nat := *)
(*   if x \in nondom_pperm p then None *)
(*   else fun_var (seq_of_pperm p) x. *)

(* Definition supportp (p : pperm) := *)
  

(* Definition eq_pperm p p' := [forall ] *)



(* Lemma fun_varK : forall s x, obind (fun_var (var_inv s)) (fun_var s x) = Some x. *)
(* Proof. *)
(* elim: s => [|[x0 y0] s ihs] x //=. *)
(* have [->|neq_xx0] := altP (x =P x0); first by rewrite eqxx. *)
(* rewrite -!fun_if !ihs. *)
(* have [eq_y0|] := altP (fun_var _ x =P y0). *)
(*   rewrite -{1}eq_y0 (inj_eq (can_inj ihs)) eq_sym (negPf neq_xx0) eqxx. *)
(*   by rewrite -eq_y0 ihs. *)
(* by move=> /negPf->; rewrite (negPf neq_xx0) ihs. *)
(* Qed. *)

(* Lemma fun_varVK s : cancel (fun_var (var_inv s)) (fun_var s). *)
(* Proof. by move=> x; rewrite -{1}[s]var_invK; apply: fun_varK. Qed. *)

(* Lemma fun_var_bij s : bijective (fun_var s). *)
(* Proof. exists (fun_var (var_inv s)); [exact: fun_varK|exact: fun_varVK]. Qed. *)

(* Lemma fun_var_nil : fun_var [::] =1 some. *)
(* Proof. done. Qed. *)

(* Lemma if_eq (X : eqType) Y (T : X -> Y) a b : *)
(*   (if a == b then T a else T b) = T b. *)
(* Proof. by case: ifP => // /eqP ->. Qed. *)

(* Lemma fun_var_cons_comp x y f a : *)
(*   fun_var ((x, y) :: f) a = fun_var [::(fun_var f x, y)] (fun_var f a).   *)
(* Proof. by rewrite /= (bij_eq (fun_var_bij _)). Qed. *)

(* Lemma fun_var_comp f g x : *)
(*   fun_var f (fun_var g x) = *)
(*   fun_var ([seq (fun_var (var_inv g) a.1, a.2) | a <- f] ++ g) x. *)
(* Proof. *)
(* elim: f => [|[a b] f ihf] //= in x *. *)
(* by rewrite -!ihf -(can2_eq (fun_varK _) (fun_varVK _)) fun_varVK. *)
(* Qed. *)

(* Lemma fun_var_eq s x y : fun_var ((x, y) :: s) x = y. *)
(* Proof. by rewrite /= eqxx. Qed. *)

(* Lemma eq_fun_var s x y z :  *)
(*   (fun_var ((x, y) :: s) z == y) = (z == x). *)
(* Proof. by rewrite (can2_eq (fun_varK _) (fun_varVK _)) fun_var_eq. Qed. *)

(* Definition eq_var_fun_var s (x y : nat) : eq_var s x y = (fun_var s x == Some y). *)
(* Proof. *)
(* elim: s => [|[a b] s ihs] //= in x y *. *)
(* have [|nxa] := altP (x =P a); have [->|nyb] //= := altP (y =P b). *)
(*   by rewrite eqxx. *)
(*   by rewrite (inj_eq Some_inj) eq_sym (negPf nyb). *)
(*   by case: ifP. *)
(* rewrite ihs; case: ifP => // /eqP->. *)
(* by rewrite (inj_eq Some_inj) eq_sym (negPf nyb). *)
(* Qed. *)

(* Lemma fun_varP s (x y : nat) : eq_var s x y -> fun_var s x = Some y. *)
(* Proof. by rewrite eq_var_fun_var => /eqP. Qed. *)

(* Lemma eq_var_eqr s x y y' : eq_var s x y -> eq_var s x y' = (y == y'). *)
(* Proof. *)
(* by move=> exy; rewrite eq_var_fun_var (fun_varP exy) (inj_eq Some_inj). *)
(* Qed. *)

(* Lemma eq_var_eql s y x x' : eq_var s x y -> eq_var s x' y = (x == x'). *)
(* Proof.  *)
(* elim: s => [|[a b] s ihs] //= in x y x' *; first by move/eqP->. *)
(* have [->|nxa] := altP (x =P a); have [->|nyb] //= := altP (y =P b). *)
(*   by rewrite eq_sym; case: (a == x'). *)
(* move/ihs->; have [<-|nxx'] := altP (x =P x'); last by rewrite !(orbF, andbF). *)
(* by rewrite (negPf nxa). *)
(* Qed. *)

(* Lemma eq_var_fun s x x' : eq_var s x (fun_var s x') -> x = x'. *)
(* Proof. *)
(* rewrite eq_var_fun_var. *)

(* Proof. by move=> /eq_var_fun_var /(bij_inj (fun_var_bij _)). Qed. *)

(* Lemma eq_var_fun_trivial s x : eq_var s x (fun_var s x). *)
(* Proof. by rewrite eq_var_fun. Qed. *)
(* Hint Resolve eq_var_fun_trivial.  *)

(* Lemma eq_var_reflP s : reflexive (eq_var s) <-> fun_var s =1 id. *)
(* Proof. *)
(* split; first by move=> eq_var_refl x; rewrite (eqP (eq_var_refl _)). *)
(* by move=> fun_var_id x; rewrite /eq_var fun_var_id. *)
(* Qed. *)

Lemma eq_var_sym s x y : eq_var (var_inv s) x y = eq_var s y x.
Proof.
by elim: s => [|[a b] s /= ->] //=; rewrite andbC [(_ == _) == _]eq_sym.
Qed.

End NominalTheory. 

(* Fixpoint alpha s t t' := *)
(*   match t, t' with *)
(*     | pVar x, pVar y => eq_var s x y *)
(*     | pLambda x u, pLambda y u' => alpha ((x, y) :: s) u u' *)
(*     | pApp u v, pApp u' v' => alpha s u u' && alpha s v v' *)
(*     | _, _ => false *)
(*   end. *)
(* Notation alpha_eq := (alpha [::]). *)

(* Local Open Scope quotient_scope. *)

(* Lemma alpha_eq_refl t : alpha_eq t t. *)
(* Proof. *)
(* have: reflexive (eq_var [::]) by exact: eqxx. *)
(* elim: t [::] => [x|u ihu v ihv|x u ihu] s s_refl //=. *)
(*   by rewrite ?ihu ?ihv. *)
(* by apply: ihu => /= y; rewrite (s_refl _) eqxx orbT. *)
(* Qed. *)
(* Hint Resolve alpha_eq_refl. *)

(* Lemma alpha_eq_sym : symmetric alpha_eq. *)
(* Proof. *)
(* move=> t t'; set f := {1}[::]; set g := {1}[::]. *)
(* have: f = var_inv g by []. *)
(* elim: t t' f g => [x|u ihu v ihv|x u ihu] [y|u' v'|y u'] f g fg_sym //=. *)
(*   by rewrite fg_sym eq_var_sym. *)
(*   by rewrite (ihu _ _ g) ?(ihv _ _ g). *)
(* by apply: ihu => /=; rewrite fg_sym. *)
(* Qed. *)
(* Hint Resolve alpha_eq_sym. *)

(* Lemma alpha_eq_trans : transitive alpha_eq. *)
(* Proof. *)
(* move=> t' t t''. *)
(* set f := {1}[::]; set g := {1}[::]; set h := {1}[::]. *)
(* have: forall x y z, eq_var f x y -> eq_var g y z -> eq_var h x z. *)
(*   by move=> x y z /= /eqP-> /eqP->. *)
(* elim: t' t t'' f g h => [y|u' ihu v' ihv|y u' ihu] *)
(*   [x|u v|x u] [z|u'' v''|z u''] f g h fg_comp //=. *)
(*   exact: fg_comp. *)
(*   move=> /andP [? ?] /andP [? ?]. *)
(*   by rewrite (ihu _ _ f g) // (ihv _ _ f g). *)
(* apply: ihu => x' y' z' /=. *)
(* case: (_ == x); case: (_ == y); case: (_ == z) => //=. *)
(* exact: fg_comp. *)
(* Qed. *)
(* Hint Resolve alpha_eq_trans. *)

(* Canonical alpha_eq_equiv := *)
(*   EquivRel alpha_eq alpha_eq_refl alpha_eq_sym alpha_eq_trans. *)

(* Definition term := {eq_quot alpha_eq}. *)
(* (* Canonical term_subType := [subType of term by %/]. *) *)
(* Definition term_eqMixin := [eqMixin of term]. *)
(* Canonical term_eqType := EqType term term_eqMixin. *)
(* Canonical term_choiceType := Eval hnf in [choiceType of term]. *)
(* Canonical term_countType := Eval hnf in [countType of term]. *)
(* Canonical term_quotType := Eval hnf in [quotType of term]. *)
(* Canonical term_eqQuotType := Eval hnf in [eqQuotType alpha_eq of term]. *)

(* Lemma alpha_eqE x y : alpha_eq x y = (x == y %[mod term]). *)
(* Proof. by rewrite piE. Qed. *)

(* Definition Var x := lift_cst term (pVar x). *)
(* Canonical pi_Var x := PiConst (Var x). *)

(* Definition App := lift_op2 term pApp. *)
(* Lemma pAppK : {morph \pi_term : x y / pApp x y >-> App x y}. *)
(* Proof. *)
(* unlock App => x y /=; apply/eqP. *)
(* by rewrite [_ == _]piE /= !alpha_eqE !reprK !eqxx. *)
(* Qed. *)
(* Canonical pi_App := PiMorph2 pAppK. *)

(* Lemma eq_alpha f g : eq_var f =2 eq_var g -> alpha f =2 alpha g. *)
(* Proof. *)
(* move=> eq_fg t t'; *)
(* elim: t t' f g eq_fg => [x|u ihu v ihv|x u ihu] [x'|u' v'|x' u'] f g eq_fg //=. *)
(*   by rewrite (ihu _ f g) // (ihv _ f g). *)
(* by apply: ihu => a b //=; rewrite eq_fg. *)
(* Qed. *)

(* Lemma alphaE f : eq_var f =2 eq_op -> alpha f =2 alpha_eq. *)
(* Proof. by rewrite -[eq_op]/(eq_var [::]) => /eq_alpha. Qed. *)

(* Definition Lambda x := lift_op1 term (pLambda x). *)
(* Lemma pLambdaK x : {morph \pi_term : u / pLambda x u >-> Lambda x u}. *)
(* Proof. *)
(* move=> u; unlock Lambda => /=; apply/eqmodP => /=; rewrite  /=. *)
(* rewrite alphaE ?alpha_eqE ?reprK // => y z /=. *)
(* have [->|neq_xy] //= := altP eqP. *)
(*   by rewrite [true == _]eq_sym eqb_id andbC andKb. *)
(* rewrite [false == _]eq_sym eqbF_neg. *)
(* by have [<-|neq_yz] //= := altP (y =P z); rewrite (andbT, andbF). *)
(* Qed. *)
(* Canonical pi_Lambda x := PiMorph1 (pLambdaK x). *)

(* Lemma pVarK n : \pi_term (pVar n) = Var n. *)
(* Proof. by rewrite !piE. Qed. *)

(* Lemma VarK n : repr (Var n) = pVar n. *)
(* Proof. *)
(* have: alpha_eq (repr (Var n)) (pVar n) by rewrite alpha_eqE reprK piE. *)
(* by case: (repr (Var n)) => //= m /eqP->. *)
(* Qed. *)

(* Lemma AppK u v : exists u' v',  *)
(*     [/\ u = \pi_term u', v = \pi_term v' & repr (App u v) = pApp u' v']. *)
(* Proof. *)
(* have: alpha_eq (repr (App u v)) (pApp (repr u) (repr v)). *)
(*   by rewrite alpha_eqE reprK -[u]reprK -[v]reprK !piE !reprK. *)
(* case: (repr (App _ _)) => //= u' v'; rewrite !alphaE //.  *)
(* by rewrite !alpha_eqE !reprK => /andP [/eqP <- /eqP <-]; exists u', v'; split. *)
(* Qed. *)

(* (* Lemma LambdaK x u : exists x' u',  *) *)
(* (*     [/\ u = \pi_term (subst x x' u')  & repr (Lambda x u) = pLambda x' u']. *) *)
(* (* Proof. *) *)
(* (* have: alpha_eq (repr (Lambda x u)) (pLambda x (repr u)). *) *)
(* (*   by rewrite alpha_eqE reprK -[u]reprK !piE !reprK. *) *)
(* (* rewrite ; case: (repr (Lambda _ _)) => //= x' u'. *) *)
(* (* Abort. *) *)

(* Definition depth := lift_fun1 term pre_depth. *)


(* Lemma pi_morph_depth : {mono \pi_term : t / pre_depth t >-> depth t}. *)
(* Proof. *)
(* by unlock depth => t /=; apply: (@alpha_depth [::]); rewrite alpha_eqE reprK. *)
(* Qed. *)
(* Canonical pi_depth := PiMono1 pi_morph_depth. *)

(* (* Definition same_vars (s s' : seq nat) := perm_eq (undup s) (undup s'). *) *)

(* (* Lemma same_vars_is_equiv : equiv_class_of same_vars. *) *)
(* (* Proof. *) *)
(* (* split=> [?|??|???];  *) *)
(* (* by [exact: perm_eq_refl|exact: perm_eq_sym|exact: perm_eq_trans]. *) *)
(* (* Qed. *) *)
(* (* Canonical same_vars_equiv := @EquivRelPack _ same_vars same_vars_is_equiv. *) *)

(* (* Definition vars := {eq_quot same_vars}. *) *)

(* (* Definition mem_vars x := lift_fun1 vars (fun s => x \in s). *) *)

(* (* Definition eqvars_class := vars. *) *)
(* (* Identity Coercion vars_of_eqvars : eqvars_class >-> vars. *) *)

(* (* Coercion pred_of_eq_vars (s : eqvars_class) : pred_class := [eta mem_vars^~ s]. *) *)

(* (* Canonical vars_predType := @mkPredType nat vars pred_of_eq_vars. *) *)
(* (* (* The line below makes mem_vars a canonical instance of topred. *) *) *)
(* (* Canonical mem_vars_predType := mkPredType mem_vars. *) *)

(* (* Lemma mem_varsK x : {mono \pi_vars : s / x \in s >-> x \in (s : vars)}. *) *)
(* (* Proof. *) *)
(* (* move=> /= s; rewrite -[LHS]/(mem_vars _ _); unlock mem_vars.  *) *)
(* (* rewrite -mem_undup -[RHS]mem_undup. *) *)
(* (* by have /eqmodP /= /perm_eq_mem -> := reprK (\pi_vars s). *) *)
(* (* Qed. *) *)
(* (* (* Canonical pi_mem_vars x := PiMono1 (mem_varsK x). *) *) *)
 
(* (* Definition cat_vars := lift_op2 vars cat. *) *)
(* (* Lemma cat_varsK : {morph \pi : x y / x ++ y >-> cat_vars x y}. *) *)
(* (* Proof. *) *)
(* (* unlock cat_vars => x y /=. *) *)
(* (* apply/eqmodP; apply: uniq_perm_eq; rewrite ?undup_uniq // => n. *) *)
(* (* by rewrite !mem_undup -/vars !mem_cat -!mem_varsK !reprK. *) *)
(* (* Qed. *) *)
(* (* Canonical pi_cat_vars := PiMorph2 cat_varsK. *) *)

(* Require Import zmodp. *)

(* Lemma pre_fv_uniq t : uniq (pre_fv t). *)
(* Proof. by elim: t => * //=; rewrite ?undup_uniq ?filter_uniq. Qed. *)

(* Fixpoint eq_var_seq v s s' := *)
(*   match s, s' with *)
(*     | x :: s, y :: s' => eq_var v x y && eq_var_seq v s s' *)
(*     | [::], [::] => true | _, _ => false *)
(*   end. *)

(* Lemma eq_var_seqE v s s' :  *)
(*   eq_var_seq v s s' = (size s == size s') && *)
(*                [forall i : 'I_(size s), eq_var v (nth 0 s i) (nth 0 s' i)]. *)
(* Proof. *)
(* elim: s s' => [|x s ihs] [|y s'] //=. *)
(*   by symmetry; apply/forallP => [] []. *)
(* rewrite ihs eqSS; have [eq_size|_] /= := altP eqP; last by rewrite andbF. *)
(* by rewrite -!(big_andE xpredT) big_ord_recl. *)
(* Qed. *)

(* Lemma eq_var_eq v y y' x x' : *)
(*   eq_var v x y -> eq_var v x' y' -> (x == x') = (y == y'). *)
(* Proof. *)
(* elim: v => [|[a b] v ihv] //=; first by move=> /eqP-> /eqP->. *)
(* have [<-|] //= := altP (_ =P a); have [<-|] //= := altP (_ =P b); *)
(* have [->|] //= := altP (x' =P _); have [->|] //= := altP (y' =P _). *)
(*   by rewrite !eqxx. *)
(*   by rewrite [x' == _]eq_sym [y' == _]eq_sym => /negPf-> /negPf->. *)
(* by move => /negPf-> /negPf->. *)
(* Qed. *)

(* Lemma nth_eq_var v x y s s' i : i < size s ->  *)
(*   eq_var v x y -> eq_var_seq v s s' -> (nth 0 s i == x) = (nth 0 s' i == y). *)
(* Proof. *)
(* move=> i_small v_xy; rewrite eq_var_seqE => /andP [/eqP ss' /forallP /= Hv]. *)
(* by have /(fun H => eq_var_eq H v_xy) := Hv (Ordinal i_small). *)
(* Qed. *)

(* Lemma size_eq_var v s' s : eq_var_seq v s s' -> size s = size s'. *)
(* Proof. by rewrite eq_var_seqE => /andP [/eqP]. Qed. *)

(* Lemma mem_eq_var v y s' x s : *)
(*   eq_var v x y -> eq_var_seq v s s' -> (x \in s) = (y \in s'). *)
(* Proof. *)
(* move=> v_xy v_ss'; have ss' := size_eq_var v_ss'. *)
(* apply/(nthP 0)/(nthP 0) => [] [i]; rewrite -?ss' => Hi Hxy. *)
(*   by exists i => //; apply/eqP; rewrite -(nth_eq_var _ v_xy v_ss') ?Hxy. *)
(* by exists i => //; apply/eqP; rewrite (nth_eq_var _ v_xy v_ss') ?Hxy. *)
(* Qed. *)
 
(* Lemma eq_var_undup v s s' : *)
(*   eq_var_seq v s s' -> eq_var_seq v (undup s) (undup s'). *)
(* Proof. *)
(* elim: s s' => [|x s ih] [|y s'] //= /andP[xy ss']. *)
(* by rewrite (mem_eq_var xy ss'); case: ifP; rewrite /= ih ?andbT. *)
(* Qed. *)

(* Lemma eq_var_cat v s1 s2 s1' s2' : size s1 = size s1' -> *)
(*   eq_var_seq v (s1 ++ s2) (s1' ++ s2') = *)
(*   (eq_var_seq v s1 s1') && (eq_var_seq v s2 s2'). *)
(* Proof. *)
(* move=> ss1; rewrite !eq_var_seqE /= -!(big_andE xpredT) !size_cat ss1. *)
(* rewrite eqn_add2l !eqxx /=; have [ss2|] := altP eqP; rewrite ?andbF ?ss2 //=. *)
(* rewrite big_split_ord /=; congr (_ && _); apply: eq_bigr => i //= _; *)
(* rewrite !nth_cat !(ss1, ss2) ?ltn_ord //=. *)
(* by rewrite addnC addnK ltnNge leq_addl. *)
(* Qed. *)

(* Lemma eq_var_catP v s1 s2 s1' s2' : *)
(*   (eq_var_seq v s1 s1') && (eq_var_seq v s2 s2') -> *)
(*   eq_var_seq v (s1 ++ s2) (s1' ++ s2'). *)
(* Proof. *)
(* by move=> /andP [Hs1 Hs2]; rewrite eq_var_cat ?Hs1 ?Hs2 ?(size_eq_var Hs1). *)
(* Qed. *)

(* Lemma eq_var_filter v y0 s' x0 s (w := (x0, y0) :: v) : *)
(*       eq_var_seq w s s' -> *)
(*       eq_var_seq v [seq x <- s | x != x0] [seq x <- s' | x != y0]. *)
(* Proof. *)
(* elim: s s' => [|x s ihs] [|y s'] //= in v w * => /andP[xy ss']. *)
(* have xy0 : eq_var w x0 y0 by rewrite /= !eqxx. *)
(* have xxyy0 := eq_var_eq xy xy0. *)
(* rewrite xxyy0; have [yy0|yy0] //= := altP eqP; rewrite ?ihs ?andbT //. *)
(* by move: xy; rewrite /w /= (negPf yy0) andbF /= => /andP[]. *)
(* Qed. *)

(* Definition fv := lift_fun1 term pre_fv. *)
(* Lemma fvK : {mono \pi : t / pre_fv t >-> fv t}. *)
(* Proof. *)
(* unlock fv => t /=. *)
(* have Ht: alpha_eq (repr (\pi_(term) t)) t by rewrite alpha_eqE reprK. *)
(* do [set f := {1}[::]; set t' := (repr (\pi t))] in Ht *. *)
(* suff : eq_var_seq f (pre_fv t') (pre_fv t). *)
(*   by elim: (pre_fv t') (pre_fv t) => [|?? ih] [|??] //= /andP[/eqP-> /ih->]. *)
(* elim: t t' f Ht => [x|u ihu v ihv|x u ihu] [y|u' v'|y u'] f //=. *)
(*   by rewrite andbT. *)
(*   by move=> /andP [u'u v'v]; rewrite eq_var_undup ?eq_var_catP ?ihu ?ihv. *)
(* by move=> u'u; rewrite eq_var_filter //= ihu. *)
(* Qed. *)
(* Canonical pi_fv := PiMono1 fvK. *)

(* (* Fixpoint preterm_rect (P : term -> Type) *) *)
(* (*   (PVar : forall n : nat, P (Var n))  *) *)
(* (*   (PApp : forall p : term, P p -> forall p0 : term, P p0 -> P (App p p0)) *) *)
(* (*   (PLambda : forall (x : nat) (p : term), P p -> P (Lambda x p)) *) *)
(* (*   (p : term) : P p := *) *)
(* (* quotW  *) *)
(* (* match (repr p) with *) *)
(* (*  | pVar n => PV n *) *)
(* (*  | pApp u v => _ *) *)
(* (*  | pLambda x u => _ *) *)
(* (* end. *) *)



(* Definition vars (s : seq (nat * nat)) := *)
(*    [seq x.1 | x <- s] ++ [seq x.2 | x <- s]. *)

(* Lemma eq_var_refl x s : x \notin vars s -> eq_var s x x. *)
(* Proof. *)
(* elim: s => [|[y1 y2] s ihs] //=. *)
(* rewrite mem_cat !map_cons /= !in_cons /= -!orbA !negb_or => /and4P []. *)
(* by move=> /negPf -> x1 /negPf -> x2 /=; rewrite ihs // mem_cat negb_or x1. *)
(* Qed. *)

(* Require Import bigenough. *)
(* Import BigEnough. *)

(* Fixpoint pvsubst s t : option preterm := *)
(* match t with *)
(*   | pVar x => if fun_var s x is Some y then Some (pVar y) else None *)
(*   | pApp u v => if (pvsubst s u, pvsubst s v) is (Some u', Some v') *)
(*                 then Some (pApp u' v') else None *)
(*   | pLambda x u => let y := fresh (pre_fv u ++ [seq x.2 | x <- s]) in *)
(*                    if pvsubst ((x, y) :: s) u is Some u' *)
(*                    then Some (pLambda y u') else None *)
(* end. *)


(* (* Fixpoint psubst s t := *) *)
(* (* match t with *) *)
(* (*   | pVar x => assoc (pVar x) s x *) *)
(* (*   | pApp u v => pApp (psubst s u) (psubst s v) *) *)
(* (*   | pLambda x u => let y := fresh (pre_fv u) in *) *)
(* (*                    pLambda y (psubst ((x, pVar y) :: s) u) *) *)
(* (* end. *) *)

(* (* Definition var_subst (s : seq (nat * nat)) := [seq (x.1, pVar x.2) | x <- s]. *) *)

(* (* Lemma var_substK s x y : assoc (pVar x) (var_subst s) y = pVar (assoc x s y). *) *)
(* (* Proof. by elim: s => [|[a b] s ihs] //=; case: ifP. Qed. *) *)

(* (* Lemma eq_cons_pv_subst x y z s t : *) *)
(* (*   pvsubst ((x, y) :: s) t -> *) *)
(* (*   obind (pvsubst [:: (y, z)]) (pvsubst ((x, y) :: s) t) = *) *)
(* (*   pvsubst ((x, z) :: s) t. *) *)
(* (* Proof. *) *)
(* (* elim: t => [//= n|//= u ihu v ihv|n u ihu] in x y z s *. *) *)
(* (*   have [|nx] //= := altP (n =P x); first by rewrite eqxx. *) *)
(* (*   case eq_sn: fun_var => [sn|] //=. *) *)
(* (*   rewrite !(inj_eq Some_inj). *) *)
(* (*   have [->|sny] //= := altP (sn =P y). *) *)
(* (*   by rewrite (negPf sny). *) *)
(* (*   have [] := (ihu x y z s, ihv x y z s). *) *)
(* (*   case eq_xysu : (pvsubst _ u) => [xysu|] //=. *) *)
(* (*   by case eq_xysv : (pvsubst _ v)=> [xysv|] //= -> // -> //. *) *)
(* (* rewrite /=. *) *)
(* (* have := (ihu n (fresh (pre_fv u)) _ ((x, y) :: s)). *) *)
(* (* case eq_xysu : (pvsubst _ u) => [xysu|] //=. *)   *)
 
(* Lemma alphaK s t t' :  *)
(*   alpha s t t' = pvsubst s t && alpha_eq (odflt (pVar 0) (pvsubst s t)) t'. *)
(* Proof. *)
(* elim: (pre_depth t) s t' {-2}t (leqnn (pre_depth t)) => [|d ihd] s t'. *)
(*   case => //= n _; case eq_a : fun_var => [a|] //=; *)
(*   by case: t' => // b; rewrite eq_var_fun_var eq_a ?(inj_eq Some_inj). *)
(* move=> u; rewrite leq_eqVlt => /orP [/eqP|/ihd]; last exact. *)
(* case: u => //= [u v|x u] [dt]. *)
(*   case eq_su : pvsubst => [su|] //=; last first. *)
(*     by case: t' => // u' v'; rewrite (ihd s u') ?eq_su // -dt leq_maxl. *)
(*   case eq_sv : pvsubst => [sv|] //=; last first. *)
(*     by case: t' => // u' v'; rewrite (ihd s v') ?eq_sv ?andbF // -dt leq_maxr. *)
(*   case: t' => // u' v'. *)
(*   by rewrite ?(ihd s, eq_su, eq_sv) //= -?dt ?(leq_maxl, leq_maxr). *)
(* case eq_su : pvsubst => [su|] //=; last first. *)
(*   case: t' => //= n u'. *)
(*   admit. *)
(* case: t' => //= n u'. *)
(* rewrite ihd ?dt // [in RHS]ihd  //=; last first. *)
(*   admit. *)
(* set c1 := (X in X && _); set c2 := (X in _ = X && _). *)
(* have eq_c12 : c1 = c2. *)
(*   admit. *)
(* rewrite -eq_c12; case c1T : c1 => //=; have: c2 by rewrite -eq_c12. *)
(* move: c1T; rewrite /c1 /c2 {c1 c2 eq_c12}. *)
(* case eq_xnsu: pvsubst => [xnsu|] //= _. *)
(* case eq_fu: pvsubst => [fu|] //= _. *)
(* apply: left_trans => //. *)


  

  



(*  rewrite ihu ?eq_su // ihv ?eq_sv. *)
(*  do [move=> /= []] in dt. *)
(*   admit. *)

(* elim: t t' => [x|u ihu v ihv|x u ihu] //= t'' in s *. *)
(*   case eq_a : fun_var => [a|] //= _. *)
(*   by case: t'' => // b; rewrite eq_var_fun_var eq_a (inj_eq Some_inj). *)
(*   case eq_su : pvsubst => [su|] //. *)
(*   case eq_sv : pvsubst => [sv|] //= _. *)
(*   by case: t'' => // u' v'; rewrite ihu ?eq_su // ihv ?eq_sv. *)
(* case eq_su : pvsubst => [su|] //= _. *)
(* case: t'' => //= n u'. *)
(* rewrite ihu /=. *)

(*   rewrite ?var_substK //=. *)
(*   elim: s => [|[a b] s ihs] //=; rewrite ?eqxx ?andbT //= ihs. *)
(*   case Ha: (x' == a) => //=. *)
(*     by rewrite ![x == _]eq_sym; case: (b == x). *)
(*   have -> /= : s = [::] by admit. *)
  
(*   by rewrite [x == _]eq_sym. *)
(*   by rewrite ihu ihv andbACA. *)
(* set y := fresh _; set y' := fresh _. *)
(* rewrite ihu; congr (_ && _). *)
(*   admit. *)
(* rewrite [RHS]ihu. *)

(*   elim: s => [|[a b] s ihs] //=; rewrite ?eqxx ?andbT //=. *)
(*   have [<-|] //= := altP (x =P a); have [<-|] //= := altP (x' =P b). *)

  

(* Definition subst s := lift_op1 term (psubst s). *)
(* Lemma substK s : {morph \pi_term : t / psubst s t >-> subst s t}. *)
(* Proof. *)
(* unlock subst => t; apply/eqmodP; rewrite /=  /=. *)
(* move/eqmodP : (esym (reprK (\pi_term t))) => /=. *)
(* elim: t (repr _) => [x|u ihu v ihv|x u ihu] [x'|u' v'|x' u'] //=. *)
(*   by move/eqP ->. *)
(*   by move=> /andP[/ihu -> /ihv ->]. *)

(* elim: s  *)



(* (* Lemma eq_fun_of s x y: eq_var s x y -> fun_var s x = y. *) *)
(* (* Proof. *) *)
(* (* elim: s => [/eqP->|[x' y'] s ihs] //= Hy; symmetry; apply/eqP; move: Hy. *) *)
(* (* by case: (x == x') => //=; case: (y == y') => //= /ihs ->. *) *)
(* (* Qed. *) *)

(* (* Definition var_rev (s : seq (nat * nat)) := map (fun x => (x.2, x.1)) s. *) *)

(* (* Lemma eq_var_sym s x y : eq_var (var_rev s) x y = eq_var s y x. *) *)
(* (* Proof. *) *)
(* (* by elim: s => [|[a b] s /= ->] //=; rewrite andbC [(_ == _) == _]eq_sym. *) *)
(* (* Qed. *) *)

(* Lemma rename_subproof x y t :  *)
(*   y \notin pre_fv t -> *)
(*   exists t', alpha_eq (pLambda x t) (pLambda y t'). *)
(* Proof. *)
(* rewrite  /=; elim: t y => [z|u ihu v ihv|z u ihu] y. *)
(*   rewrite in_cons /= orbF eq_sym => yz. *)
(*   exists (pVar (if z == x then y else z)). *)
(*   by case: (_ == x) yz => /=; case: (z == y); rewrite ?eqxx //=. *)
(* rewrite /= mem_undup mem_cat => /norP [/ihu [u' Hu'] /ihv [v' Hv']]. *)
(* by exists (pApp u' v'); rewrite Hu' Hv'. *)
(* rewrite [_ \in _]/= mem_filter negb_and negbK => /orP [/eqP<-|/ihu [u' Hu']]. *)
(*   pose_big_enough y'. *)
(*     have [|u' Hu']:= ihu y'; first by rewrite fresh. *)
    
(*   exists (pLambda y' u'); rewrite /=. *)
(*   rewrite (@eq_alpha _ [:: (x, y')]) // => a b /=. *)
(*   have [->|] //= := altP (a =P _); have [->|] //= := altP (b =P _). *)
(*     rewrite !(@ltn_eqF _ y') // ?andbF . *)

(*   admit. *)
(* exists (pLambda z u'); rewrite /=. *)
(* Abort. *)

(* Lemma reterm_rect_subproof :  *)
(* {elim : forall (P : term -> Type), *)
(*   (forall n : nat, P (Var n)) -> *)
(*   (forall p : term, P p -> forall p0 : term, P p0 -> P (App p p0)) -> *)
(*   (forall (x : nat) (p : term), P p -> P (Lambda x p)) -> *)
(*   forall p : term, P p |  *)
(*   forall P PV PA PL, *)
(*   [/\ forall n, elim P PV PA PL (Var n) = (PV n), *)
(*   forall u Pu v Pv, elim P PV PA PL (App u v) = (PA u Pu v Pv) & *)
(*   forall x u Pu, elim P PV PA PL (Lambda x u) = (PL x u Pu)] *)
(* }. *)
(* Proof. *)
(* eexists (fun P PV PA PL =>  *)
(* quotP (fun (p : preterm) => match p with  *)
(*  | pVar n => _ *)
(*  | pApp u v => _ *)
(*  | pLambda x u => _ *)
(* end)) => /= P PV PA PL. *)
(* split => [n|u Pu v Pv|x u Pu]. *)
(*   rewrite VarK. *)

(*  rewrite ?(VarK, AppK). LambdaK). *)
(* move=> PVar PApp PLam; elim/quotW => /=. *)
(* elim => [n|u ihu v ihv|x u ihu] /=. *)
(*   by rewrite pVarK. *)
(*   by rewrite pAppK; apply: PApp. *)
(* by rewrite pLambdaK /= -/term; apply: PLam. *)
(* Qed. *)
