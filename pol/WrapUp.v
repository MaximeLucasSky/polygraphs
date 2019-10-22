Require Import Basics.
Require Import Paths.
Require Import HIT.
Require Import Polygraphs.
Require Import PolyMorphs.
Require Import Adjunction.


Definition Counit_inject (n : nat) (T : Type) : 
  compose  (CounitA (S n) (Counit T n)) (injectPol (Forget T n) (ForgetA (Counit T n) (S n)))
           = (Counit T n).
Proof.
  destruct n.
  - simpl. exact 1.
  - simpl.
    unfold compose. apply funext. simple refine (eqMorphPushout _ _ _).
    + intro b1. reflexivity.
    + intro b2. simpl. reflexivity.
    + intros [a a']. simpl. exact ((concat_1p _)).
Defined.


    



Lemma Forget_composeM (n : nat) ( T T' T'' : Type) (f : T -> T') (f' : T' -> T'') :
  ComposeM (ForgetM n f) (ForgetM n f') = ForgetM n (compose f' f).
Admitted.

Fixpoint ForgetTriangular (n : nat) (T : Type) {struct n} :
  ComposeM (Unit (Forget T n)) (ForgetM n (Counit T n)) = fstd IdAndFreeM (Forget T n).
Proof.
Admitted.