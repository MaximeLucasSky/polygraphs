Require Import Paths.
Require Import HIT.
Require Import Polygraphs.
Require Import PolyMorphs.




Definition EmptyA (n : nat) (T : Type) : Aug T n := mkAug False (fun x => False_rect _ x.1).

Definition Empty {n : nat} (p : Pol n) : Pol (S n) :=  Ext p (EmptyA (S n) (Free p)). 

Definition FreeEmptyA (n : nat) (T : Type) : T -> FreeA (EmptyA n T) := inl.

Definition FreeEmpty {n :nat} (p : Pol n) : Free p -> Free (Empty p) := FreeEmptyA (S n) (Free p).


Lemma ap_along_id {A : Type} {x y : A} (p : x = y) : ap (fun x => x) p = p.
Proof.
  destruct p. exact 1.
Defined.

Definition IdMA {n : nat} {T : Type} (aug : Aug T n)  : MAug (fun x => x) aug aug := mkMAug (fun x => x) (fun  _ _ => 1).

Definition FreeIdMA {n : nat} {T : Type} (aug : Aug T n) : FreeMA (IdMA aug) = (fun x => x).
Proof.
  apply funext.
  simple refine (eqMorphPushout _ _ _ ).
  - intro b1. simpl. reflexivity.
  - intro b2. simpl. destruct b2.  reflexivity.
  - simpl. intros [a a'].
    simple refine ( _ @ (concat_p1 _)^). 
    simple refine (ap_along_id _ @ _).
    exact Pushout_rect_compute_coh ^. 
Defined.

  
Fixpoint IdAndFreeM {n : nat} : {f : forall p : Pol n, MPol p p | forall p : Pol n, FreeM (f p) = (fun x => x)}.
Proof.
  destruct n.
  - simple refine (mkDPair _ _); intro p;  destruct p using case0.
    + econstructor.  exact (fun x => x).
    + exact 1.
  -  simple refine (mkDPair _ _ ); intro p; destruct p using caseS'.
    + unshelve econstructor.
      * exact (fstd (IdAndFreeM n) p).
      * match goal with
        | |- MAug _ aug aug => simple refine (transport (fun W => MAug W aug aug)  _ _)
        end.
        -- exact (fun x => x).
        -- exact ((sndd (IdAndFreeM n) p)^).
        -- simpl. exact (IdMA aug).
    + simpl. 
      simple refine ((image_transport _ _ _ _) @ (FreeIdMA _) ).
Defined.

Definition EmptyMA (n : nat) (T : Type) (aug : Aug T n) : MAug (fun x => x) (EmptyA n T) aug.
Proof.
  simpl. unshelve econstructor. 
  - exact (False_rect _).
  - simpl. intro. contradiction.
Defined.

Lemma EmptyExtensionInitial {n : nat} {p : Pol n} (aug : Aug (Free p) (S n)) : MPol (Empty p) (Ext p aug).
Proof.
  unfold Empty.
  unshelve econstructor.
  - exact (fstd IdAndFreeM p).
  - simpl. change (MAug (FreeM (fstd IdAndFreeM p)) (EmptyA (S n) (Free p)) aug).
    simple refine (transport (fun W => MAug W (EmptyA (S n) (Free p)) aug) _ _).
    + exact (fun x => x).
    + exact ((sndd IdAndFreeM p) ^).
    + exact (EmptyMA _ _ _). 
Defined.

Definition injectA {n : nat} {F : Type} (aug : Aug F n) : F -> FreeA aug := compose (FreeMA (EmptyMA n F aug)) (FreeEmptyA n F).

Definition injectPol {n :nat} (p : Pol n) (aug : Aug (Free p) (S n)) : Free p -> Free (Ext p aug) := injectA aug.



Definition UnitA  {n : nat} {F T : Type}  (aug : Aug F n) (f : FreeA aug -> T) : MAug (injectA aug) aug (ForgetA f n).
Proof.
  unshelve econstructor.
  - intro e. simple refine (mkPullB _ _ _).
    + intro b. apply f. simpl. simple refine (inr _). exact (e, b).
    + intro. simple refine (inl _). exact (d aug (e, X)).
    + apply funext. intro. unfold nFaces. unfold compose. exact (ap f (incoh (e, x))^).
  - simpl. intros. reflexivity.
Defined.

Definition UnitBisA {n : nat} {F : Type} (aug : Aug F (S n)) (f : F -> (Free (Forget (FreeA aug) n)))
           (H : compose (Counit (FreeA aug) n) f = injectA aug):
  MAug f aug (ForgetA (Counit (FreeA aug) n) (S n)).
Proof.
  unshelve econstructor.
  -  intro e. simpl. simple refine (mkPullB _ _ _).
     + intro x. exact (inr (e, x)).
     + intro x. simpl.
       apply f. exact (d aug (e, x)).
     + unfold nFaces. unfold compose. apply funext. intro x.
       simple refine (_ @ (ap (fun W => W (d aug (e, x))) H^)).
       exact ((incoh (e, x))^).
  - reflexivity.
Defined.

Definition TriangleA  {n : nat} {F T : Type}  (aug : Aug F n) (f : FreeA aug -> T) : compose (CounitA n f) (FreeMA (UnitA aug f)) = f.
Proof.
  apply funext. simple refine (eqMorphPushout _ _ _).
  - reflexivity.
  - intro b2. unfold compose. simpl. destruct b2. reflexivity.
  - intros [a a']. simpl.
    simple refine ( _ @ (concat_p1 _)^).
    match goal with
    | |- _ = ap (compose ?f ?g) ?p => simple refine (_ @ (ap_compose g f p)^)
    end.
    unfold compose.
    match goal with
    | |- _ = ap ?f _ => simple refine (_ @ ap (ap f) Pushout_rect_compute_coh^)
    end.
    simpl.
    unfold CounitA.
    simple refine (_ @ Pushout_rect_compute_coh^). simpl.
    simple refine (_ @ (concat_ap_V _ _)^).
    simple refine (_ @ (ap (fun W => W ^) (funextcompute _ a')^)). simpl.
    match goal with
    | |- _ = (ap f ?p ^)^ => 
      simple refine (_ @ ap (fun W => W^ ) (concat_ap_V f p)^);
        exact ((concat_VV _)^)
    end.
Defined.


Lemma TriangleABis {n : nat} {F : Type} (aug : Aug F (S n)) (f : F -> (Free (Forget (FreeA aug) n)))
           (H : compose (Counit (FreeA aug) n) f = injectA aug): 
           compose (CounitA (S n) (Counit (FreeA aug) n))
                   (FreeMA (UnitBisA aug f H)) = (fun x : FreeA aug => x).
Proof.
  apply funext. simple refine (eqMorphPushout _ _ _).
  - intro b1. unfold compose. simpl. exact (ap (fun W => W b1) H).
  - intro b2. unfold compose. simpl. destruct b2. reflexivity.
  - intros a. unfold compose. simpl.
    simple refine (_ @ (concat_p1 _)^).
    match goal with
    | |- _ = ap (fun x => CounitA ?a1 ?a2  (@?W x)) (incoh a) =>
      change (ap (fun x => CounitA a1 a2 (W x)) (incoh a)) with
          (ap (compose (CounitA a1 a2) W) (incoh a));
        simple refine (_ @ (ap_compose W (CounitA a1 a2) (incoh a))^)
    end. unfold compose. unfold CounitA.
    match goal with
    | |- _ = ap ?f _  => simple refine (_ @ (ap (fun W => ap f W) Pushout_rect_compute_coh^))
    end. simpl.
    match goal with
    | |- _ = ap (Pushout_rect ?a1 ?a2 ?a3) (incoh ?a4) =>
      simple refine (_ @ (Pushout_rect_compute_coh (f1 := (fun x  => pi2 x.1 x.2)) )^)
    end.
    simpl.
    match goal with
    | |- _ = ap ?f ?p ^ => simple refine (_ @ (concat_ap_V f p)^)
    end.
    match goal with
    | |- _ = (ap (fun W => W a.2) (funext ?p))^ => 
      simple refine (_ @ (ap (fun W => W^) (funextcompute p a.2)^))
    end.
    match goal with
    | |- ?p @ _ = _ => simple refine ((ap (fun W => p @ W) (ap_id _)) @ _)
    end.
    simple refine (_ @ (concat_V _ _)^).
    match goal with
    | |- _ = ?p ^ @ ?q ^ ^ =>
      simple refine (_ @ ap (fun W => p ^ @ W) (concat_VV _)^);
        simple refine (_ @ ap (fun W => W ^ @ q) (concat_ap_V _ _)^);
        exact (ap (fun W => W @ q) (concat_VV _)^)
    end.
Defined.


Fixpoint UnitPol {n : nat} (p : Pol n) {struct n} : {f :  MPol p (Forget (Free p) n) |
                                                              compose (Counit (Free p) n) (FreeM f) = (fun x => x)}.
Proof.
  destruct n.
  - simple refine (mkDPair _ _).
    + destruct p using case0. econstructor. exact (fun x => x).
    + destruct p using case0. exact 1.
  - simple refine (mkDPair _ _); destruct p as [p aug] using caseS'.
    + simpl. unshelve econstructor. 
      * exact (ComposeM (fstd (UnitPol n p)) (ForgetM n (injectPol p aug) ) ).
      * simpl.  simple refine (UnitBisA _ _ _).
        match goal with
          |- compose ?f _ = _ => simple refine (ap (fun W => compose f W) (FreeComposeM _ _) @ _)
        end.
        match goal with
        | |- compose ?f (compose ?g ?h) = _ => change (compose f (compose g h)) with (compose (compose f g) h);
                                               simple refine (ap (fun W => compose W h) (CounitM _ _) @ _)
        end.
        match goal with
        | |- compose (compose ?f ?g) ?h = _ => change (compose (compose f g) h) with (compose f (compose g h));
                                           exact (ap (fun W => compose f W) (sndd (UnitPol _ _)))
        end.
    + simpl. 
      simple refine (TriangleABis _ _ _).
Defined.

Notation Unit p := (fstd (UnitPol p)).
Notation FreeTriangular p := (sndd (UnitPol p)).
