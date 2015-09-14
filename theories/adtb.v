From Ssreflect
Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq fintype.
From MathComp
Require Import finfun finset generic_quotient bigop tuple.

Require Import finmap finsfun finperm nominal utilitaires.

Require Import EqdepFacts.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope finperm_scope with fperm.
Local Open Scope finperm_scope.
Local Open Scope fset.
Local Open Scope quotient_scope.

Import Key.Exports.

Section ADTB_signature.

Record signature := 
  Signature {
      cons : eqType ; 
      bcons : eqType ;
      nonrecursive : cons -> eqType ; 
      recursive : cons -> nat ;
      bnonrecursive : bcons -> eqType ;
      bbrecursive : bcons -> nat ; (* where the name binds *)
      ubrecursive : bcons -> nat (* where the name doesn't bind *)
}.

End ADTB_signature.

Section ADTB_def.

Context (s : signature).

Inductive rADTB :=
|rCons : forall (c : cons s),
           nonrecursive c -> ilist rADTB (recursive c) -> rADTB
|rBCons : forall (c : bcons s) (x : atom),
           bnonrecursive c -> 
           ilist rADTB (bbrecursive c) -> 
           ilist rADTB (ubrecursive c) -> rADTB.

(* TODO : encodage des rADTB *)
Definition rADTB_encode : rADTB -> GenTree.tree atom. Admitted.
Definition rADTB_decode : GenTree.tree atom -> rADTB. Admitted.
Lemma rADTB_codeK : cancel rADTB_encode rADTB_decode. Admitted.

Definition rADTB_eqMixin := CanEqMixin rADTB_codeK.
Canonical rADTB_eqType := EqType rADTB rADTB_eqMixin.
Definition rADTB_choiceMixin := CanChoiceMixin rADTB_codeK.
Canonical rADTB_choiceType := ChoiceType rADTB rADTB_choiceMixin.
Definition rADTB_countMixin := CanCountMixin rADTB_codeK.
Canonical rADTB_countType := CountType rADTB rADTB_countMixin.

End ADTB_def.

Arguments rCons [s] c _ _.
Arguments rBCons [s] c x _ _ _.

Section Induction_principle.

Context (s : signature) (P : rADTB s -> Prop).
Hypothesis Cons_case : forall (c : cons s) (v : nonrecursive c) 
                              (r : ilist (rADTB s) (recursive c)),
                         All P r -> P (rCons c v r).
Hypothesis BCons_case : forall (c : bcons s) (x : atom) (v : bnonrecursive c)
                               (rb : ilist (rADTB s) (bbrecursive c))
                               (ru : ilist (rADTB s) (ubrecursive c)),
                         All P rb -> All P ru -> P (rBCons c x v rb ru).


Fixpoint rADTB_ind' (t : rADTB s) : P t :=
  let F := (fix ilist_radtb_ind {n} (ls : ilist (rADTB s) n) : All P ls :=
           match ls with
             |Nil => I
             |u:::q => conj (rADTB_ind' u) (ilist_radtb_ind q)
           end) in
  match t with
    |rCons c v r => Cons_case v (F r)
    |rBCons c x v rb ru => BCons_case x v (F rb) (F ru)
  end.

End Induction_principle.
