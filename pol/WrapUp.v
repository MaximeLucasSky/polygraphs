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
    + intros [a a']. simpl. exact ((concat_1p _) @ (concat_p1 _)^).
Defined.

Definition ComposeMA_assoc {n :nat}  {F1 F2 F3 F4 : Type} {f1 : F1 -> F2} {f2 : F2 -> F3} {f3 : F3 -> F4}
         {aug1 : Aug F1 n} {aug2 : Aug F2 n} {aug3 : Aug F3 n} {aug4 : Aug F4 n}
         (G1 : MAug f1 aug1 aug2) (G2 : MAug f2 aug2 aug3) (G3 : MAug f3 aug3 aug4):
  transport (fun W => MAug W aug1 aug4) (compose_assoc f3 f2 f1) (ComposeMA G1 (ComposeMA G2 G3)) =  (ComposeMA (ComposeMA G1 G2) G3).
Proof.
  destruct aug1 as [E1 d1], aug2 as [E2 d2], aug3 as [E3 d3], aug4 as [E4 d4].
  destruct G1 as [G1E coh1] using caseMAug.
  destruct G2 as [G2E coh2] using caseMAug.
  destruct G3 as [G3E coh3] using caseMAug.
  simpl.
  simple refine (eq_MA _ _ _ _).
  - exact 1.
  - intros e x.
    simpl.
    simple refine ((concat_1p _) @ _ ).
    match goal with
    | |- ?p @ ap ?f (?q @ ?r) = _ => simple refine (ap (fun W => p @ W) (ap_concat f q r) @ _)
    end.
    match goal with
    | |- ?p @ (?q @ ap ?f (ap ?g ?r)) = _ => exact (ap (fun W => p @ (q @ W)) (ap_compose g f r)^ @ (assoc _ _ _))
    end.
Defined.

Lemma forall_eq_rect {A : Type} {B : A -> Type} (f : forall a : A, B a) (P : forall g : (forall a : A, B a),  ((forall a : A, f a = g a)  -> Type))
      (H : P f (fun a => 1)) g p : P g p.
Proof.
  exact (forall_eq_destruct f (fun G => P (fstd G) (sndd G)) H (mkDPair g p)).
Defined.

Lemma forall_eq_destruct {A : Type} {B : A -> Type} (f g h : forall a : A, B a) (p : forall a : A, f a = g a) (q : forall a : A, g a = h a) :
  FunExtDep (fun a => p a @ q a) = FunExtDep p @ FunExtDep q.
Proof.
  simple refine (forall_eq_rect _ (fun h (q : forall a : A, g a = h a) =>  FunExtDep (fun a : A => p a @ q a) = FunExtDep p @ FunExtDep q) _ _ q).
  simpl.
  simple refine (ap (fun W => FunExtDep W) (FunExtDep (fun a : A => concat_p1 (p a))) @ _).
  simple refine (_ @ ap (fun W => FunExtDep p @ W) (FunExtDep_refl)^).
  exact ((concat_p1 _)^).
Defined.

Opaque eq_MA.

Lemma Free_composeMA_assoc {n :nat}  {F1 F2 F3 F4 : Type} {f1 : F1 -> F2} {f2 : F2 -> F3} {f3 : F3 -> F4}
         {aug1 : Aug F1 n} {aug2 : Aug F2 n} {aug3 : Aug F3 n} {aug4 : Aug F4 n}
         (G1 : MAug f1 aug1 aug2) (G2 : MAug f2 aug2 aug3) (G3 : MAug f3 aug3 aug4):
  ap FreeMA (ComposeMA_assoc G1 G2 G3) = (FreeComposeMA G1 (ComposeMA G2 G3))
                                           @ ap (fun W => compose W (FreeMA G1)) (FreeComposeMA G2 G3) 
                                           @ ap (fun W => compose (FreeMA G3) W) (FreeComposeMA G1 G2)^
                                         @ (FreeComposeMA (ComposeMA G1 G2) G3)^ .
Proof.
 destruct aug1 as [E1 d1], aug2 as [E2 d2], aug3 as [E3 d3], aug4 as [E4 d4]. 
 destruct G1 as [G1E coh1] using caseMAug.
 destruct G2 as [G2E coh2] using caseMAug.
 destruct G3 as [G3E coh3] using caseMAug.
 unfold ComposeMA_assoc. simpl. 
 match goal with 
 | |- ap FreeMA (eq_MA ?a1 ?a2 ?a3 ?a4) = _ => simple refine ( (ap_FreeMA (F := F1) (F' := F4)_ _ a1 a2 a3 a4) @ _)
 end. Opaque FreeMA_eq.
 Admitted.
 
Lemma transport_compose {A A' : Type} (f : A -> A') (P : A' -> Type) {x y : A} (p : x = y) (u : P (f x)):
  transport (compose P f) p u = transport P (ap f p) u.
Proof.
  destruct p.
  reflexivity.
Defined.

Definition eq_MPol (n : nat) (P P' : Pol n) (aug : Aug (Free P) (S n)) (aug' : Aug (Free P') (S n))
           (f f' : MPol P P') (MF : MAug (FreeM f) aug aug') (MF' : MAug (FreeM f') aug aug')
           (p : f = f') (q : transport (fun W => MAug (FreeM W) aug aug') p  MF = MF') : ExtM f MF = ExtM f' MF'.
Proof.
  destruct p.
  destruct q.
  reflexivity.
Defined.



Lemma transport_transport (A B : Type) (f : A -> B) (P : B -> Type) (x y : A) (z : B) (p : x = y) (q : f x = z) (px : P z) :
  transport (fun W => P (f W)) p (transport P q^ px) = transport P (q^ @ ap f p) px.
Proof.
  destruct p. destruct q. reflexivity.
Defined.

Fixpoint ComposeM_assoc {n :nat} (p q r s : Pol n) (F : MPol p q) (G : MPol q r) (H : MPol r s) {struct n}:
  {c : ComposeM F (ComposeM G H) = ComposeM (ComposeM F G) H | ap FreeM c =
                                                               (FreeComposeM F (ComposeM G H))
                                                                 @ ap (fun W => compose W (FreeM F)) (FreeComposeM G H) 
                                                                 @ ap (fun W => compose (FreeM H) W) (FreeComposeM F G)^
                                                               @ (FreeComposeM (ComposeM F G) H)^}.
Proof.
  destruct n.
  - destruct p using case0. destruct q using case0. destruct r using case0. destruct s using case0.
    destruct F as [f] using (caseM0 _ _). destruct G as [g] using (caseM0 _ _). destruct H as [h] using (caseM0 _ _).
    simpl. unshelve econstructor.
    + reflexivity.
    + reflexivity.
  - destruct p as [p augp] using (caseS' n).  destruct q as [q augq] using (caseS' n).  destruct r as [r augr] using (caseS' n).  destruct s as [s augs] using (caseS' n).
    destruct F as [F Faug] using (caseMS' _ _ _ _ _).
    destruct G as [G Gaug] using (caseMS' _ _ _ _ _).
    destruct H as [H Haug] using (caseMS' _ _ _ _ _).
    simpl.
    unshelve econstructor.
    + simple refine (eq_MPol _ _ _ _ _ _ _ _ _ _ _).
      * exact (fstd (ComposeM_assoc n p q r s F G H)).
      * simpl. refine ((transport_transport _ _ _ _ _ _ _ _ _ _) @ _).
        rewrite (sndd (ComposeM_assoc n p q r s F G H)). simpl.

      
Admitted.

SearchAbout transport.

Lemma Forget_composeM (n : nat) ( T T' T'' : Type) (f : T -> T') (f' : T' -> T'') :
  ComposeM (ForgetM n f) (ForgetM n f') = ForgetM n (compose f' f).
Admitted.

Fixpoint ForgetTriangular (n : nat) (T : Type) {struct n} :
  ComposeM (Unit (Forget T n)) (ForgetM n (Counit T n)) = fstd IdAndFreeM (Forget T n).
Proof.
  destruct n.
  - exact 1.
  -  simpl. simple refine (eq_MPol _ _ _ _ _ _ _ _ _ _ _).
     + refine ((ComposeM_assoc _ _ _ _ _ _ _)^ @ _).
       unfold injectPol.
       refine ((ap (fun W => ComposeM (Unit (Forget T n)) W) (Forget_composeM _ _ _ _ _ _)) @ _).
       change (injectA (ForgetA (Counit T n) (S n))) with (injectPol _ (ForgetA (Counit T n) (S n))).
       refine ((ap (fun W => ComposeM (Unit (Forget T n)) (ForgetM n W)) (Counit_inject _ _ )) @ _).
       exact (ForgetTriangular n T).
    + simpl.