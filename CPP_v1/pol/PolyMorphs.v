Require Import Basics.
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
  - intro. exact (pi1 X.1 X.2).
  - intros [x e]. simpl. exact (f_equal (fun W => W e) (coh x)^).
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


Lemma eq_MA {F F' : Type} {n : nat} {f : F -> F'} {aug : Aug F n} {aug' : Aug F' n} (G H : aug - f -- aug')
      (p : ME G = ME H )
      (q : forall e x, ((f_equal (fun W => d aug' (W e, x)) p) @ (Md H e x)) =  Md G e x) :
    G = H :> MAug f aug aug'.
Proof.
  destruct H as [HME HMd].
  simpl in  p. destruct p.
  assert (Md G = HMd).
  {
    repeat (apply FunExtDep; intro). simpl in *.
    exact ((q x x0)^ @ concat_1p _).
  }
  now destruct H. 
Defined.


Lemma FreeMA_inr {F F' : Type} {n : nat} {f : F -> F'} {aug : Aug F n} {aug' : Aug F' n}
      (G H : aug - f -- aug')
      (p : ME G = ME H )
      (q : forall e x,  (f_equal (fun W => d aug' (W e, x)) p) @ (Md H e x) = (Md G e x))
      (x : E aug × Ball n) :
  FreeMA G (inr x) = inr (ME G x.1, x.2).
Proof.
  reflexivity.
Defined.

Lemma eq_MA_inr {F F' : Type} {n : nat} {f : F -> F'} {aug : Aug F n} {aug' : Aug F' n} 
      (G H : aug - f -- aug')
      (p : ME G = ME H )
      (q : forall e x,  (f_equal (fun W => d aug' (W e, x)) p) @ (Md H e x) = (Md G e x))
      (x : E aug × Ball n) :
  f_equal (fun T => FreeMA T (inr x)) (eq_MA G H p q) = f_equal (fun T => inr (T x.1, x.2)) p.
Proof.
  simpl. unfold eq_MA. destruct H as [HE Hd]. simpl in *.
  destruct p. simpl in *.
  match goal with
  | |- f_equal _ (match ?a return _ with |_ => _ end q) = 1 => destruct a
  end.
  reflexivity.
Defined.

Lemma FreeMA_eq  {F F' : Type} {n : nat} {f : F -> F'} {aug : Aug F n} {aug' : Aug F' n} 
      (G H : aug - f -- aug')
      (p : ME G = ME H )
      (q : forall e x,  (f_equal (fun W => d aug' (W e, x)) p) @ (Md H e x) = (Md G e x)) :
  FreeMA G = FreeMA H :> ([aug]* -> [aug']* ).
Proof.
  destruct H as [HME HMd].
  simpl in  p. destruct p.
  assert (Md G = HMd).
  {
    repeat (apply FunExtDep; intro). simpl in *.
    exact ((q x x0)^ @ concat_1p _).
  }
  now destruct H.                   
Defined.



Lemma ap_FreeMA  {F F' : Type} {n : nat} {f : F -> F'} {aug : Aug F n} {aug' : Aug F' n} 
      (G H : aug - f -- aug')
      (p : ME G = ME H )
      (q : forall e x,  (f_equal (fun W => d aug'  (W e, x)) p) @ (Md H e x) = (Md G e x)):
  f_equal FreeMA (eq_MA G H p q) = FreeMA_eq G H p q :> (FreeMA G = FreeMA H :> (FreeA aug -> FreeA aug')).
Proof.
  destruct H as [HE Hd]. simpl in *.
  destruct p. simpl in q.
  set (q' := fun e x => (concat_1p _ )^ @ q e x).
  assert ((fun e x => (concat_1p _) @ (q' e x)) = q).
  { apply FunExtDep. intro. apply FunExtDep. intro. subst q'. simpl.
    rewrite assoc. rewrite concat_pV. exact (concat_1p _).
  }
  clearbody q'. destruct H.
  refine (destruct_fun_eq (fun G1 G2 q =>
                             f_equal FreeMA (eq_MA (mkMAug (ME G) G2) (mkMAug (ME G) G1) 1 (fun e x => concat_1p _ @ q e x )) =
                             FreeMA_eq (mkMAug (ME G) G2)  (mkMAug (ME G) G1) 1 (fun e x => concat_1p _ @ q e x ))
                          _ q').
  intro. clear Hd q'. simpl.
  match goal with
  | |- f_equal FreeMA
         (match ?f in (_ = y) return _ with | _ => _ end _) = _ => destruct f
  end. reflexivity.
Defined.


Definition ForgetMA (n : nat) {T T' : Type} {F F' : Type} (g : F -> T) (g' : F' -> T')  (Ff: F -> F') (Tf : T -> T')
           (H : (compose g' Ff) = (compose Tf g)) : MAug Ff (ForgetA g n) (ForgetA g' n).
Proof.
  unshelve econstructor.
  - intro. simple refine (mkPullB _ _ _).
    + exact (compose Tf (pi1 X)).
    + exact (compose Ff (pi2 X)).
    + unfold nFaces.
      unfold compose.
      simple refine (_ @ (f_equal (fun W => compose W (pi2 X)) H^)).
      exact (f_equal (fun W => compose Tf W) (coh X)).
  - reflexivity.
Defined.

Definition pre_ap_counit_coh {T F : Type} (n : nat)  ( f : F -> T ) (a : E (ForgetA f n) × Sphere n) :
  CounitA n f (inl (d (ForgetA f n) a)) = CounitA n f (inr {| fst := a.1; snd := Faces n a.2 |}) :=
  f_equal (fun T => T a.2) (coh a.1)^.
  
Lemma ap_counit_coh {T F : Type} (n : nat)  ( f : F -> T ) (a : E (ForgetA f n) × Sphere n) :
  (f_equal (fun x : [ForgetA f n ]* => CounitA n f x) (incoh a)) =  f_equal (fun T => T a.2) (coh a.1)^.
Proof.
  exact Pushout_rect_compute_coh.
Defined.

Definition NaturalMA (n : nat) {T T' : Type} {F F' : Type} (g : F -> T) (g' : F' -> T')  (Ff: F -> F') (Tf : T -> T')
           (H : (compose g' Ff) = (compose Tf g)) :
  compose (CounitA n g') (FreeMA (ForgetMA n g g' Ff Tf H))  = compose Tf (CounitA n g).
Proof.
  apply funext. simple refine (eqMorphPushout _ _ _).
  - unfold compose. simpl. intro b. exact (f_equal (fun W => W b) H).
  - reflexivity.
  - intro a. unfold compose. simpl.
    match goal with
    | |- _ = f_equal (fun x => CounitA n g' (?f x)) ?p =>
      simple refine (_ @ (ap_compose f (CounitA n g') p)^)  
    end.
    unfold FreeMA.
    simple refine (_ @ (f_equal (fun W => f_equal (CounitA n g') W) Pushout_rect_compute_coh^)).
    simple refine (_ @ (ap_concat _ _ _)^).
    simple refine (_ @ (concat_1p _)^).
    simple refine (_ @ Pushout_rect_compute_coh^).
    simpl.
    simple refine (_ @ (concat_ap_V _ _)^). 
    match goal with
    | |- _ = (f_equal ?f (?p @ ?q))^ => simple refine (_ @ (f_equal (fun W => W^) (ap_concat f p q)^))
    end.
    simple refine (_ @ (concat_V _ _)^).
    match goal with
    | |- _ = (f_equal ?f (f_equal ?g (?p ^))) ^ @ ?q =>
      simple refine (_ @ (f_equal (fun W => W ^ @ q) (ap_compose g f (p ^)))); 
        simple refine (_ @ (f_equal (fun W => W ^ @ q) (concat_ap_V (compose f g) p)^));
        simple refine (_ @ f_equal (fun W => W @ q) (concat_VV _)^)
    end. 
    match goal with
      | |- _ = ?p @ (f_equal ?f (f_equal ?g ?q)) ^ => 
      simple refine (_ @ (f_equal (fun W => p @ W ^) (ap_compose g f q)))
    end.
    match goal with
    | |- ?p @ f_equal (fun x => Tf (@?f x)) ?q = _ =>
      simple refine (f_equal (fun W => p @ W) (ap_compose f Tf q) @ _)
    end.
    unfold compose. 
    match goal with
    | |- ?p @ f_equal Tf _ = _ => simple refine (f_equal (fun W => p @ f_equal Tf W) (ap_counit_coh _ _ _) @ _)
    end. simpl.
    match goal with
    | |- ?p @ f_equal ?f (f_equal ?g ?q ^) = _ =>
      simple refine (f_equal (fun W => p @ f_equal f W) (concat_ap_V _ _) @ _);
        simple refine (f_equal (fun W => p @ W) (concat_ap_V _ _) @ _);
        exact (f_equal (fun W => p @ W ^) (ap_compose g f q)^ )
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
