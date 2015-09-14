From Ssreflect
Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq fintype.
From MathComp
Require Import bigop  finfun finset generic_quotient tuple.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Definition maxlist l := foldr maxn 0 l.

Lemma maxlist_leqP l n : reflect (forall x, x \in l -> x <= n)
                                 (maxlist l <= n).
Proof.
apply: (iffP idP); elim: l => //.
  move => m l IHl /=.  
  rewrite geq_max => /andP [m_leq_n maxl_leq_n] p.
  rewrite in_cons => /orP. case.
    by move/eqP ->.
  exact: IHl.
move => m l IHl Hml /=.
rewrite geq_max. apply/andP; split.
  exact/Hml/mem_head.
apply IHl => p pl.
apply Hml. by rewrite in_cons pl orbT.
Qed.

Lemma maxlist_map_leqP {A : eqType} (l : seq A) n (f : A -> nat) :
  reflect (forall x, x \in l -> f x <= n)
          (maxlist (map f l) <= n).
Proof.
apply: (iffP idP).
  move/maxlist_leqP => Hl x xl.
  exact/Hl/map_f.
move => Hl. apply/maxlist_leqP => y /mapP [x] xl ->.
exact: Hl.
Qed.

Lemma in_maxlist l x : x \in l -> x <= maxlist l.
Proof.
elim: l => //= a l IHl.
rewrite in_cons => /orP. case.
  move/eqP ->. by rewrite leq_maxl.
move/IHl => x_leq_maxl. apply (@leq_trans (maxlist l)) => //.
by rewrite leq_maxr.
Qed.

Fixpoint all2 {A : eqType} (p : A -> A -> bool) (l1 l2 : seq A) :=
  match l1, l2 with
    |[::], [::] => true
    |a::q, b::r => (p a b) && all2 p q r
    |_, _ => false
  end.

Fixpoint all2_prop {A B : Type} (p : A -> B -> Prop) (l1 : seq A) (l2 : seq B) :=
  match l1, l2 with
    |[::], [::] => True
    |a::q, b::r => (p a b) /\ all2_prop p q r
    |_, _ => False
  end.

Lemma all2P {A : eqType} (p : A -> A -> bool) l1 l2 : 
  reflect (all2_prop p l1 l2) (all2 p l1 l2).
Proof.
apply: (equivP idP).
elim: l1 l2 => [[|a2 l2]|] //= a1 l1 IHl1 [|a2 l2] //.
split.
  move/andP => [? ?]; split =>//; exact/IHl1.
move => [? ?]; apply/andP; split => //.
exact/IHl1.
Qed.

Lemma eq_in_all2_prop {A : eqType} (s1 s2 : seq A) (P1 P2 : A -> A -> Prop) :
  (forall x y, x \in s1 -> y \in s2 -> (P1 x y <-> P2 x y)) -> 
  all2_prop P1 s1 s2 <-> all2_prop P2 s1 s2.
Proof.
elim: s1 s2. by case.
move => a1 s1 IHl. case => // a2 s2 P1_eq_P2 /=.
split; move => [? ?].
all: split; try (by apply P1_eq_P2; rewrite ?mem_head).
all: apply IHl => // x y xs1 ys2; apply P1_eq_P2.
all: by rewrite in_cons (xs1, ys2) orbT.
Qed.

Lemma eq_in_all2 {A : eqType} (s1 s2 : seq A) (p1 p2 : A -> A -> bool) : 
  {in s1 & s2, p1 =2 p2} -> all2 p1 s1 s2  = all2 p2 s1 s2.
Proof.
elim: s1 s2. by case.
move => a1 s1 IHl. case => // a2 s2 p1_eq_p2 /=. 
rewrite p1_eq_p2 ?mem_head // IHl //.
move => x1 x2 x1s1 x2s2. apply p1_eq_p2;
by rewrite inE (x1s1, x2s2) orbT.
Qed.

Lemma all2_eq {A : eqType} (s1 s2 : seq A) (p1 p2 : A -> A -> bool) :
  p1 =2 p2 -> all2 p1 s1 s2 = all2 p2 s1 s2.
Proof.
move => p1_eq_p2.
apply eq_in_all2 => t1 t2 _ _. 
exact/p1_eq_p2.
Qed.

Lemma all2_prop_eq {A : Type} (s1 s2 : seq A) :
  all2_prop eq s1 s2 <-> s1 = s2.
Proof.
elim: s1 s2 => [[|? ?]|a1 s1 IHs1 [|a2 s2]] //=.
split => [[a1_eq_a2 eq_s1s1]|a1s1_eq_a2s2].
  by rewrite a1_eq_a2 (iffLR (IHs1 s2)).
injection a1s1_eq_a2s2 => <- ->; split => //.
exact/IHs1.
Qed.

Lemma all2_map {A B : eqType} (s1 s2 : seq A) (p : B -> B -> bool) (f g : A -> B) :
  all2 p (map f s1) (map g s2) = all2 (fun x y => p (f x) (g y)) s1 s2.
Proof.
elim: s1 s2. by case.
move => a1 s1 IH. case => // a2 s2 /=.
by rewrite IH.
Qed.

Lemma all2_prop_map {A B : Type} {s1 s2 : seq A} {P : B -> B -> Prop} {f g : A -> B} :
  all2_prop (fun x y => P (f x) (g y)) s1 s2 -> all2_prop P (map f s1) (map g s2).
Proof.
elim: s1 s2. by case.
move => a1 s1 IH. case => // a2 s2 /= [? ?]; split => //.
exact/IH.
Qed.

Lemma all2_mapl {A : eqType} (s : seq A) (p : A -> A -> bool) (f : A -> A) :
  all2 p (map f s) s = all2 (fun x y => p (f x) y) s s.
Proof. by rewrite -{2}[s]map_id all2_map. Qed.

Lemma all2_mapr {A : eqType} (s : seq A) (p : A -> A -> bool) (f : A -> A) :
  all2 p s (map f s) = all2 (fun x y => p x (f y)) s s.
Proof. by rewrite -{1}[s]map_id all2_map. Qed.

Lemma all2_refl {A : eqType} (s : seq A) (p : A -> A -> bool) :
  {in s, reflexive p} -> all2 p s s. 
Proof.
elim: s => // a l IHl reflp /=.
rewrite reflp /=; last exact: mem_head.
apply IHl => x xl. apply reflp.
by rewrite in_cons xl orbT.
Qed.

Definition switch {A B} (f : A -> A -> B) x y := f y x.

Lemma all2_sym {A : eqType} (s1 s2 : seq A) (p q : A -> A -> bool) :
  {in s1 & s2, p =2 switch q} -> all2 p s1 s2 = all2 q s2 s1.
Proof.
elim: s1 s2. by case.
move => a1 s1 IH. case => // a2 s2 p_switch /=.
rewrite p_switch ?mem_head //.
rewrite IH // => t1 t2 t1s1 t2s2.
apply p_switch; by rewrite in_cons (t1s1, t2s2) orbT.
Qed.  

Lemma all2_prop_trans {A : eqType} (s1 s2 s3 : seq A) (P1 P2 P3 : A -> A -> Prop) :
  (forall x1 x2 x3, x1 \in s1 -> x2 \in s2 -> x3 \in s3 ->
     (P1 x1 x2 -> P2 x2 x3 -> P3 x1 x3)) -> 
     (all2_prop P1 s1 s2) -> (all2_prop P2 s2 s3) -> (all2_prop P3 s1 s3).  
Proof.
Proof.
elim: s1 s2 s3 => [[|a2 s2] [|a3 s3]|a1 s1 IHs1 [|a2 s2] [|a3 s3]] //= Htrans. 
move => [p1a1a2 p1s1s2] [p2a2a3 p2s2s3]; split.
  apply (@Htrans a1 a2 a3) => //; exact/ mem_head.
apply (@IHs1 s2 s3) => // x1 x2 x3 x1s1 x2s2 x3s3.
apply Htrans; by rewrite in_cons (x1s1, x2s2, x3s3) orbT.
Qed.

Lemma all2_trans {A : eqType} (s1 s2 s3 : seq A) (p1 p2 p3 : A -> A -> bool) :
  (forall x1 x2 x3, x1 \in s1 -> x2 \in s2 -> x3 \in s3 ->
     (p1 x1 x2 -> p2 x2 x3 -> p3 x1 x3)) -> 
     (all2 p1 s1 s2) -> (all2 p2 s2 s3) -> (all2 p3 s1 s3).  
Proof.
move => H /all2P Hs1s2 /all2P Hs2s3; apply/all2P. 
move: Hs1s2 Hs2s3. exact/all2_prop_trans.
Qed.

Lemma all2_quot {A : eqType} {B} (s1 s2 : seq A) (p : A -> A -> bool) (f : A -> B):
  (forall x y, x \in s1 -> y \in s2 -> p x y -> f x = f y) -> all2 p s1 s2 ->
  map f s1 = map f s2.
Proof.
elim: s1 s2 => [[|? ?]|a1 s1 IHs1 [|a2 s2]] //= f_equalizer => /andP [pa1a2 ps1s2].
rewrite (f_equalizer a1 a2) ?mem_head // (IHs1 s2) // => x1 x2 x1s1 x2s2.
by apply/f_equalizer; rewrite in_cons (x1s1, x2s2) orbT.
Qed.

Lemma and_iff_congr A B C D : (A <-> B) -> (C <-> D) -> (A /\ C) <-> (B /\ D). 
Proof.
move => A_eq_B C_eq_D.
apply: (@iff_trans _ (B /\ C)).
  exact: and_iff_compat_r.
exact: and_iff_compat_l.
Qed. 

Lemma forall_iff {A} (P Q : A -> Prop) : 
  (forall x, P x  <-> Q x) -> ((forall x, P x) <-> (forall x, Q x)).
Proof.
move => all_P_eq_Q.
split => H x.    
all: exact/all_P_eq_Q. 
Qed.

Section Ilist.
Variable A : Type.

Inductive ilist : nat -> Type :=
  |Nil : ilist 0
  |Cons : forall (h : A) {n : nat}, ilist n -> ilist (n.+1).

End Ilist.

Arguments Nil [A].
Notation " a ::: q " := (Cons a q) (right associativity, at level 70).

Section Ilist_all.

Variable T : Type.
Variable P : T -> Prop.

Fixpoint All n (ls : ilist T n) : Prop :=
  match ls with
    |Nil => True
    |t:::q => P t /\ All q
  end.
End Ilist_all.