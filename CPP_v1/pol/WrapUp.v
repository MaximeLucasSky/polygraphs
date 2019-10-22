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

Definition ComposeMA_assoc {n :nat}  {F1 F2 F3 F4 : Type} {f1 : F1 -> F2} {f2 : F2 -> F3} {f3 : F3 -> F4}
         {aug1 : Aug F1 n} {aug2 : Aug F2 n} {aug3 : Aug F3 n} {aug4 : Aug F4 n}
         (G1 : MAug f1 aug1 aug2) (G2 : MAug f2 aug2 aug3) (G3 : MAug f3 aug3 aug4):
  (ComposeMA G1 (ComposeMA G2 G3)) =  (ComposeMA (ComposeMA G1 G2) G3).
Proof.
  simpl.
  simple refine (eq_MA _ _ _ _).
  - exact 1.
  - intros e x.
    simpl.
    refine (concat_1p _ @ _).
    match goal with
    | |- ?p @ f_equal ?f (?q @ ?r) = _ => simple refine (f_equal (fun W => p @ W) (ap_concat f q r) @ _)
    end.
    match goal with
    | |- ?p @ (?q @ f_equal ?f (f_equal ?g ?r)) = _ => exact (f_equal (fun W => p @ (q @ W)) (ap_compose g f r)^ @ (assoc _ _ _))
    end.
Defined.


Lemma ap_FreecomposeMA_inl {n :nat}  {F1 F2 F3 : Type} {f1 : F1 -> F2} {f2 : F2 -> F3}
         {aug1 : Aug F1 n} {aug2 : Aug F2 n} {aug3 : Aug F3 n} 
         (G1 : MAug f1 aug1 aug2) (G2 : MAug f2 aug2 aug3) (x : F1) :
  f_equal (fun T => T (inl x)) (FreeComposeMA G1 G2) = 1.
Proof.
  simpl.
  unfold FreeComposeMA. rewrite funextcompute. reflexivity.
Defined.


Lemma ap_FreecomposeMA_inr {n :nat}  {F1 F2 F3 : Type} {f1 : F1 -> F2} {f2 : F2 -> F3}
         {aug1 : Aug F1 n} {aug2 : Aug F2 n} {aug3 : Aug F3 n} 
         (G1 : MAug f1 aug1 aug2) (G2 : MAug f2 aug2 aug3) (x : (E aug1) × Ball n) :
  f_equal (fun T => T (inr x)) (FreeComposeMA G1 G2) = 1.
Proof.
  simpl.
  unfold FreeComposeMA. rewrite funextcompute. reflexivity.
Defined.
    



Lemma Free_composeMA_assoc {n :nat}  {F1 F2 F3 F4 : Type} {f1 : F1 -> F2} {f2 : F2 -> F3} {f3 : F3 -> F4}
         {aug1 : Aug F1 n} {aug2 : Aug F2 n} {aug3 : Aug F3 n} {aug4 : Aug F4 n}
         (G1 : MAug f1 aug1 aug2) (G2 : MAug f2 aug2 aug3) (G3 : MAug f3 aug3 aug4):
  f_equal FreeMA (ComposeMA_assoc G1 G2 G3) = (((FreeComposeMA G1 (ComposeMA G2 G3)
                                           @ f_equal (fun W => compose W (FreeMA G1)) (FreeComposeMA G2 G3)) 
                                           @ f_equal (fun W => compose (FreeMA G3) W) (FreeComposeMA G1 G2)^)
                                         @ (FreeComposeMA (ComposeMA G1 G2) G3)^) .
Proof.
  apply eq_fun.
  unshelve refine (Pushout_rect_dep _ _ _ _ ).
  - intro x.
    refine ((ap_compose FreeMA _ (ComposeMA_assoc G1 G2 G3))^ @ _).  simpl.
    refine (f_equal_constant _ _ @ _).
    match goal with
    | |- 1 = f_equal ?f (((?p1 @ ?p2) @ ?p3) @ ?p4) => refine (_ @ (ap_concat _ _ _)^);
                                                  refine (_ @ f_equal (fun T => T @ (f_equal f p4)) (ap_concat f (p1 @ p2) p3)^);
                                                  refine (_ @ f_equal (fun T => (T @ (f_equal f p3)) @ (f_equal f p4)) (ap_concat f p1 p2)^)
    end.
    unfold compose in *.
    match goal with
    | |- 1 = ?a1 @ (f_equal _ (FreeComposeMA ?G1 ?G2)^) => 
      refine (_ @ (f_equal (fun T => a1 @ T) (concat_ap_V _ (FreeComposeMA G1 G2))^));
        refine (_ @  ( f_equal (fun T => a1 @ T^) (ap_FreecomposeMA_inl G1 G2 x)^))
    end. 
    simpl.
    match goal with
    | |- 1 = ((?a1 @ f_equal ?f (f_equal ?g ?h)) @ ?a2) =>
      refine (_ @ f_equal (fun T => ((a1 @ T) @ a2)) (ap_compose g f h))
    end.
    
    match goal with
    | |- 1 =  ((?a1 @ ?a2) @  f_equal ?f (f_equal ?g ?h)) =>
      refine (_ @ f_equal (fun T => (a1 @ a2) @ T) (ap_compose g f h))
    end.
    match goal with
    | |- 1 = ((?q1 @ ?q2) @ f_equal ?f ?p1^) =>
      refine (_ @ f_equal (fun T => ((q1 @ q2) @ T)) (concat_ap_V f p1)^)
    end. 
    match goal with
      |- 1 = ?p @ (f_equal _ ?q)^ =>
      refine (_ @ f_equal (fun T => p @ T^) (ap_compose (fun x0 => x0 (inl x)) (FreeMA G3) q)^)
    end.
    simpl.
    match goal with
    | |- 1 = ?a1 @ (f_equal ?f (f_equal _ (FreeComposeMA ?G1 ?G2))) ^ =>
      refine (_ @ f_equal (fun T => a1 @ (f_equal f T) ^) (ap_FreecomposeMA_inl G1 G2 x)^)
    end. simpl. 
    match goal with
    | |- 1 = ?a1 @ (f_equal _ (FreeComposeMA ?G1 ?G2)) =>
      refine (_ @ f_equal (fun T => a1 @ T) (ap_FreecomposeMA_inl G1 G2 (f1 x))^)
    end. simpl.
    match goal with
    | |- 1 = (f_equal _ (FreeComposeMA ?G1 ?G2)) =>  exact (ap_FreecomposeMA_inl G1 G2 x)^
    end.
  - intro b.
    refine ((ap_compose FreeMA _ (ComposeMA_assoc G1 G2 G3))^ @ _). 
    match goal with
    | |- _ = f_equal ?f (((?p1 @ ?p2) @ ?p3) @ ?p4) =>
      refine (_ @ (ap_concat f _ _)^);
        refine (_ @ f_equal (fun T => T @ (f_equal f p4)) (ap_concat f (p1 @ p2) p3)^);
        refine (_ @ f_equal (fun T => (T @ (f_equal f p3)) @ (f_equal f p4)) (ap_concat f p1 p2)^)
    end.
    refine (eq_MA_inr _ _ _ _ _ @ _). simpl.
    match goal with
    | |- 1 = (((?a1 @ f_equal ?f (f_equal ?g ?h)) @ ?a2)  @ ?a3) => refine (_ @ f_equal (fun T => ((a1 @ T) @ a2) @ a3) (ap_compose g f h))
    end.
    match goal with
    | |- 1 =  ((?a1 @ ?a2) @ f_equal ?f (f_equal ?g ?h)) @ ?a3 => refine (_ @ f_equal (fun T => ((a1 @ a2) @ T @ a3)) (ap_compose g f h))
    end.
    match goal with
    | |- 1 = ((?q1 @ ?q2) @ f_equal ?f ?p1^) @ f_equal ?g ?p2^ =>
      refine (_ @ f_equal (fun T => ((q1 @ q2) @ f_equal f p1^) @ T) (concat_ap_V g p2)^);
        refine (_ @ f_equal (fun T => (((q1 @ q2) @ T) @ (f_equal g p2)^)) (concat_ap_V f p1)^)
    end.

    match goal with
    | |- 1 = ?a1 @ (f_equal _ (FreeComposeMA ?G1 ?G2))^ =>
      refine( _ @ (f_equal (fun T => a1 @ T^) (ap_FreecomposeMA_inr G1 G2 b)^))
    end.
    simpl.

    match goal with
      |- 1 = ?p @ (f_equal _ ?q)^ =>
      refine (_ @ f_equal (fun T => p @ T^) (ap_compose (fun x0 => x0 (inr b)) (FreeMA G3) q)^)
    end.
    match goal with
    | |- 1 = ?a1 @ (f_equal ?a2 (f_equal _ (FreeComposeMA ?G1 ?G2))) ^  =>
      refine (_ @ f_equal (fun T => a1 @ (f_equal a2 T) ^) (ap_FreecomposeMA_inr G1 G2 b)^)
    end. simpl.
    
    match goal with
    | |- 1 = ?a1 @ (f_equal _ (FreeComposeMA ?F1 ?F2)) =>  refine (_ @ f_equal (fun T => a1 @ T) (ap_FreecomposeMA_inr F1 F2 (ME G1 b.1, b.2 ))^)
    end. simpl.
    match goal with
    | |- 1 = (f_equal _ (FreeComposeMA ?G1 ?G2))  =>  exact ((ap_FreecomposeMA_inr G1 G2 b)^)
    end. 
  - intro a. refine (transport_lemma_dep _ _ _ _ _ _).
    admit.
Admitted.


Definition eq_MPol (n : nat) (P P' : Pol n) (aug : Aug (Free P) (S n)) (aug' : Aug (Free P') (S n))
           (f f' : MPol P P') (MF : MAug (FreeM f) aug aug') (MF' : MAug (FreeM f') aug aug')
           (p : f = f') (q : eq_rect (fun W => MAug (FreeM W) aug aug')  MF p = MF') : ExtM f MF = ExtM f' MF'.
Proof.
  destruct p.
  destruct q.
  reflexivity.
Defined.

Fixpoint ComposeM_assoc {n :nat} (p q r s : Pol n) (F : MPol p q) (G : MPol q r) (H : MPol r s) {struct n}:
  {c : ComposeM F (ComposeM G H) = ComposeM (ComposeM F G) H | f_equal FreeM c =
                                                               (FreeComposeM F (ComposeM G H))
                                                                 @ f_equal (fun W => compose W (FreeM F)) (FreeComposeM G H) 
                                                                 @ f_equal (fun W => compose (FreeM H) W) (FreeComposeM F G)^
                                                               @ (FreeComposeM (ComposeM F G) H)^}.
Proof.
Admitted.

Lemma Forget_composeM (n : nat) ( T T' T'' : Type) (f : T -> T') (f' : T' -> T'') :
  ComposeM (ForgetM n f) (ForgetM n f') = ForgetM n (compose f' f).
Admitted.

Fixpoint ForgetTriangular (n : nat) (T : Type) {struct n} :
  ComposeM (Unit (Forget T n)) (ForgetM n (Counit T n)) = fstd IdAndFreeM (Forget T n).
Proof.
Admitted.