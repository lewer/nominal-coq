From Ssreflect
Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq fintype.
From MathComp
Require Import bigop  finfun finset generic_quotient perm tuple fingroup.

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

Fixpoint all2_prop {A : eqType} (p : A -> A -> Prop) (l1 l2 : seq A) :=
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

Lemma all2_map {A : eqType} (s1 s2 : seq A) (p : A -> A -> bool) (f g : A -> A) :
  all2 p (map f s1) (map g s2) = all2 (fun x y => p (f x) (g y)) s1 s2.
Proof.
elim: s1 s2. by case.
move => a1 s1 IH. case => // a2 s2 /=.
by rewrite IH.
Qed.

Lemma and_iff_congr A B C D : (A <-> B) -> (C <-> D) -> (A /\ C) <-> (B /\ D). 
Proof.
move => A_eq_B C_eq_D.
apply: (@iff_trans _ (B /\ C)).
  exact: and_iff_compat_r.
exact: and_iff_compat_l.
Qed. 