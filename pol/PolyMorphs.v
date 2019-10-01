Require Import Paths.
Require Import HIT.
Require Import Polygraphs.

(* Morphism of Polygraphs *)



Definition ForgetA {T F: Type} (f : F -> T )  (n : nat)  : Aug F n.
Proof.
  simple refine (mkAug _ _).
  - simple refine (PullB _ _).
    + exact (Ball n -> T).
    + exact (Sphere n -> F).
    + exact (Sphere n -> T).
    + exact (nFaces n T).
    + exact (compose f).
  - intros [x e]. exact (pi2 x e).
Defined.


Definition CounitA {T F : Type} (n : nat)  ( f : F -> T ) : FreeA (ForgetA f n) -> T.
Proof.
  simple refine (Pushout_rect _ _ _).
  - exact f.
  - intro. exact (pi1 (fst X) (snd X)).
  - intros [x e]. simpl. exact (ap (fun W => W e) (coh x)^).
Defined.

Fixpoint ForgetAndCounit (n : nat) : {p : forall T : Type, Pol n | forall T : Type, Free (p T) -> T}.
Proof.
  destruct n.
  - simple refine (mkDPair _ _ ); intro T.
    + exact (Disc T).
    + exact (fun x => x).
  - simple refine (mkDPair _ _); intro T.
    + simple refine (Ext _ _).
      * exact (fstd (ForgetAndCounit n) T).
      * exact (ForgetA (sndd (ForgetAndCounit n) T) (S n)).    
    +  simpl. exact (CounitA (S n) (sndd (ForgetAndCounit n) T)).
Defined.

Notation Forget T n := (fstd (ForgetAndCounit n) T).
Notation Counit T n := (sndd (ForgetAndCounit n) T).


Opaque ForgetAndCounit.




(* Lemma eq_DPair (A : Type) ( P : A -> Type) (x x' : A) (y : P x) (y' : P x') (p : x = x') (q : p # y = y') : (x,y) = (x',y'). *)
(* Proof. *)
(*   destruct p. exact (ap (fun W => (x,W)) q).  *)
(* Defined. *)

Lemma eq_MA {F F' : Type} {n : nat} {f : F -> F'} {E E' : Type} {d : E * Sphere n -> F} {d' : E' * Sphere n -> F'}
      {GE HE : E -> E'} (Gcoh :  forall e x, d' (GE e, x) = f (d (e, x))) (Hcoh : forall e x, d' (HE e, x) = f (d (e, x)))
      (p : GE = HE )
      (q : forall e x,  (ap (fun W => d' (W e, x)) p) @ (Hcoh e x) = (Gcoh e x)) :
    (mkMAug GE Gcoh) = (mkMAug HE Hcoh) :> MAug f (mkAug E d) (mkAug E' d').
Proof.
  destruct p.
  assert (Gcoh = Hcoh).
  {
    repeat (apply FunExtDep; intro).
    destruct (q x x0). apply concat_1p.
  }
  destruct H. reflexivity.
Defined.


Lemma FreeMA_eq  {F F' : Type} {n : nat} {f : F -> F'} {E E' : Type} {d : E * Sphere n -> F} {d' : E' * Sphere n -> F'}
      {GE HE : E -> E'} (Gcoh :  forall e x, d' (GE e, x) = f (d (e, x))) (Hcoh : forall e x, d' (HE e, x) = f (d (e, x)))
      (p : GE = HE) (q : forall e x,  (ap (fun W => d' (W e, x)) p) @ (Hcoh e x) = (Gcoh e x)) :
  FreeMA (mkMAug GE Gcoh) = FreeMA (mkMAug HE Hcoh) :> (FreeA (mkAug E d) -> FreeA (mkAug E' d')).
Proof.
  destruct p.
  simpl in q.
  assert (Gcoh = Hcoh).
  {
    repeat (apply FunExtDep; intro).
    destruct (q x x0). apply concat_1p.
  }
  destruct H. reflexivity.
Defined.


Lemma eq_concat {A : Type} {x y y' z: A} (p : x = y) (p': x = y') (q : y = z) (q' : y' = z) (Hy : y = y') : p @ Hy = p' -> q = Hy @ q' -> p @ q = p' @ q'.
Proof.
  intros.
  exact ((ap (fun W => p @ W) H0) @ (assoc p Hy q') @ (ap (fun W => W @ q') H)).
Defined.
  
Lemma ap_ap_compose {T0 T1 T2 T3: Type} (F: T1 -> T2) (G : T2 -> T3) {x y : T0} (H : T0 -> T1) (p : x = y) :
  ap_compose F G (ap H p) = ((ap_compose H (compose G F) p)^ @ (ap_compose (compose F H) G p) @ ap (fun W => (ap G) W) (ap_compose H F p)).
Proof.
  destruct p. reflexivity.
Defined.


Lemma destruct_fun_eq {E X} {A : E -> X -> Type}
      (P : forall G1 G2 q, Type) (H : forall G, P G G (fun e x => 1))
  {G1 : forall e x, A e x} {G2 : forall e x, A e x} (q : forall e x, G1 e x = G2 e x): P G1 G2 q.
Proof.
  set (q' := FunExtDep (fun e => (FunExtDep (fun x => q e x)))).
  assert ((fun e x => (ap (fun W => W e x) q')) = q).
  { subst q'. repeat (apply FunExtDep; intro).
    change (fun W : forall (x1 : E) (x2 : X), A x1 x2 => W x x0) with (compose (fun W : forall x2, A x x2 => W x0)  (fun W : forall x1 x2, A x1 x2 => W x)).
    rewrite ap_compose.
    unfold compose.
    rewrite (ap_FunExt (fun e => FunExtDep (fun x1 : X => q e x1)) x).
    rewrite ap_FunExt. reflexivity.
  }
  clearbody q'. destruct H0. destruct q'. apply H.
Defined.

Lemma ap_FreeMA  {F F' : Type} {n : nat} {f : F -> F'} {E E' : Type} {d : E * Sphere n -> F} {d' : E' * Sphere n -> F'}
      (GE HE : E -> E') (Gcoh :  forall e x, d' (GE e, x)= f (d (e, x))) (Hcoh : forall e x, d' (HE e, x) = f (d (e, x)))
      (p : GE = HE) (q : forall e x,  (ap (fun W => d' (W e, x)) p) @ (Hcoh e x) = (Gcoh e x)) :
  ap FreeMA (eq_MA Gcoh Hcoh p q) = FreeMA_eq Gcoh Hcoh p q :> (FreeMA (mkMAug GE Gcoh) = FreeMA (mkMAug HE Hcoh) :> (FreeA (mkAug E d) -> FreeA (mkAug E' d'))).
Proof.
  destruct p. simpl in q.
  set (q' := fun e x => (concat_1p _ )^ @ q e x).
  assert ((fun e x => (concat_1p _) @ (q' e x)) = q).
  { apply FunExtDep. intro. apply FunExtDep. intro. subst q'. simpl.
    rewrite assoc. rewrite concat_pV. exact (concat_1p _).
  }
  clearbody q'. destruct H.
  refine (destruct_fun_eq (fun G1 G2 q =>
                             ap FreeMA (eq_MA G2 G1 1 (fun (e : E) (x : Sphere n) => (concat_1p (G1 e x)) @ q e x)) =
                             FreeMA_eq G2 G1 1 (fun (e : E) (x : Sphere n) => (concat_1p (G1 e x)) @ q e x))
                          _ q').
  intro. clear Gcoh Hcoh q'. simpl.
  destruct (FunExtDep
      (fun x : E =>
       FunExtDep (fun x0 : Sphere n => match concat_1p (G x x0) @ 1 in (_ = y) return (y = G x x0) with
                                       | 1 => concat_1p (G x x0)
                                       end))). reflexivity.
Defined.



Definition ForgetMA (n : nat) {T T' : Type} {F F' : Type} (g : F -> T) (g' : F' -> T')  (Ff: F -> F') (Tf : T -> T')
           (H : (compose g' Ff) = (compose Tf g)) : MAug Ff (ForgetA g n) (ForgetA g' n).
Proof.
  unshelve econstructor.
  - intro. simple refine (mkPullB _ _ _).
    + exact (compose Tf (pi1 X)).
    + exact (compose Ff (pi2 X)).
    + unfold nFaces.
      simple refine (_ @ (compose_assoc _ _ _)^).
      simple refine (_ @ (ap (fun W => compose W (pi2 X)) H^)).
      simple refine (_ @ (compose_assoc _ _ _)).
      simple refine (_ @ (ap (fun W => compose Tf W) (coh X))).
      unfold nFaces.
      exact (compose_assoc  _ _ _).
  - simpl. reflexivity.
Defined.

Definition NaturalMA (n : nat) {T T' : Type} {F F' : Type} (g : F -> T) (g' : F' -> T')  (Ff: F -> F') (Tf : T -> T')
           (H : (compose g' Ff) = (compose Tf g)) :
  compose (CounitA n g') (FreeMA (ForgetMA n g g' Ff Tf H))  = compose Tf (CounitA n g).
Proof.
  apply funext. simple refine (eqMorphPushout _ _ _).
  - unfold compose. simpl. intro b. exact (ap (fun W => W b) H).
  - reflexivity.
  - intros [a a']. unfold compose. simpl.
    simple refine (_ @ (concat_p1 _)^).
    match goal with
    | |- _ = ap (fun x => CounitA n g' (?f x)) ?p =>
      simple refine (_ @ (ap_compose f (CounitA n g') p)^)  
    end.
    match goal with
    | |- _ = compose ?f _ _ => simple refine (_ @ (ap (fun W => f W) Pushout_rect_compute_coh^))
    end.
    simple refine (_ @ (ap_concat _ _ _)^).
    simple refine (_ @ (concat_1p _)^).
    simple refine (_ @ Pushout_rect_compute_coh^).
    simpl. unfold compose_assoc.
    simple refine (_ @ (concat_ap_V _ _)^).
    match goal with
    | |- _ = (ap ?f (((1 @ ?p @ 1) @ ?q) @ 1))^ =>
      simple refine (_ @ (ap (fun W => (ap f W)^) (concat_p1 _)^));
        simple refine (_ @ (ap (fun W => (ap f (W @ q))^) (concat_p1 _)^));
        simple refine (_ @ (ap (fun W => (ap f (W @ q))^) (concat_1p _)^))
    end.
    match goal with
    | |- _ = (ap ?f (?p @ ?q))^ => simple refine (_ @ (ap (fun W => W^) (ap_concat f p q)^))
    end.
    simple refine (_ @ (concat_V _ _)^).
    match goal with
    | |- _ = (ap ?f (ap ?g (?p ^))) ^ @ ?q =>
      simple refine (_ @ (ap (fun W => W ^ @ q) (ap_compose g f (p ^)))); 
        simple refine (_ @ (ap (fun W => W ^ @ q) (concat_ap_V (compose f g) p)^));
        simple refine (_ @ ap (fun W => W @ q) (concat_VV _)^)
    end. 
    match goal with
    | |- _ = ?p @ (ap ?f (ap ?g ?q)) ^ =>
      change (ap f (ap g q)) with (compose (ap f) (ap g) q)
    end.
    match goal with
      | |- _ = ?p @ (compose (ap ?f) (ap ?g) ?q) ^ => 
      simple refine (_ @ (ap (fun W => p @ W ^) (ap_compose g f q)))
    end.
    match goal with
    | |- ?p @ ap (fun x => Tf (@?f x)) ?q = _ =>
      simple refine (ap (fun W => p @ W) (ap_compose f Tf q) @ _)
    end.
    unfold compose. unfold CounitA. simpl. destruct a. simpl.
    match goal with
    | |- ?p @ ap Tf _ = _ => simple refine (ap (fun W => p @ ap Tf W) Pushout_rect_compute_coh @ _)
    end. simpl.
    match goal with
    | |- ?p @ ap ?f (ap ?g ?q ^) = _ =>
      simple refine (ap (fun W => p @ ap f W) (concat_ap_V _ _) @ _);
        simple refine (ap (fun W => p @ W) (concat_ap_V _ _) @ _);
        exact (ap (fun W => p @ W ^) (ap_compose g f q)^ )
    end.
Defined.


Fixpoint ForgetFunctorialAndNatural (n : nat) {struct n}:
  {ForgetM : forall (T T' : Type) (f : T -> T'), MPol (Forget T n) (Forget T' n) |
   forall (T T' : Type) (f : T -> T'), compose (Counit T' n) (FreeM (ForgetM T T' f)) = compose f (Counit T n)}.
Proof.
  destruct n.
  - simple refine (mkDPair _ _); intros T T' f.
    + econstructor. exact f.
    + exact 1.
  - simple refine (mkDPair _ _); intros T T' f.
    + unshelve econstructor. 
      * exact (fstd (ForgetFunctorialAndNatural n) _ _ f).
      * cbn. simple refine (ForgetMA (S n) _ _ _ f _). simpl. 
        match goal with
        | |- compose (sndd (?f n)  T')  _  = _  => change (sndd (f n) T') with (Counit T' n)
        end.
        exact (sndd (ForgetFunctorialAndNatural n) _ _ f).
    + simple refine ((NaturalMA (S n) _ _ _ _ _) @ _). reflexivity.
Defined.

         
Notation ForgetM n f := (fstd (ForgetFunctorialAndNatural n) _ _ f).
Notation CounitM n f := (sndd (ForgetFunctorialAndNatural n) _ _ f).