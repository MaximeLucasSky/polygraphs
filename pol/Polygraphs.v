Require Import Basics.
Require Import Paths.
Require Import HIT.

(** This file contains the definition of the category of polygraphs, together with the Free functor on it. 
More precisely we define successively:
  - polygraphs 
  - morphisms of polygraphs
  - composition of morphisms of polygraphs      
  - the identity morphism of polygraphs.
Each concept is defined first for augmentations, then for polygraphs, together with the correponding action of the free functor.

We also sketch the proof of the associativity of the composition **)


Set Primitive Projections.

(** Polygraphs **)

Record Aug (F : Type) (n : nat) :=
              mkAug {
                  E : Type;
                  d : E × Sphere n -> F
                }.

Arguments mkAug {_ _} _ _.
Arguments E {_ _} _.
Arguments d {_ _} _.


Definition FreeA {F : Type} {n : nat} (aug : Aug F n) : Type :=
  Pushout (d aug) (fun x  => (x.1 , Faces n x.2) : (E aug) × Ball n).
  

Notation "[ aug ]*" := (FreeA aug).

Inductive Pol : nat -> Type :=
|Disc : Type -> Pol 0
|Ext {n : nat} (P : Pol n) (aug : Aug (Free P) (S n)) : Pol (S n)
fix Free {n : nat} (P : Pol n) : Type :=
       match P with
       | Disc A => A
       | Ext _ _ aug => [ aug ]*
       end.

Opaque Free.
Arguments Free {_} _.

Definition tr {n : nat} (P : Pol n) : Pol (pred n) :=
  match P with
  | Disc E => Disc False
  | Ext P' aug =>  P'
  end.


Definition PAug {n : nat} (P : Pol n) : Aug (Free (tr P)) n :=
  match P with
  | Disc E => mkAug False (fun x => x.1)
  | Ext P aug => aug
  end.

Coercion PAug : Pol >-> Aug.


Definition case0 (P : Pol 0 -> Type) (H : forall (T : Type), P (Disc T))  (p : Pol 0) : P p := 
  match p with
  |Disc T => H T
  |_ => tt
  end.


Definition caseS' {n : nat} (p : Pol (S n)) :
  forall (P : Pol (S n) -> Type) (H : forall (p : Pol n) (aug : Aug (Free p) (S n)), P (Ext p aug)), P p :=
  match p with
  |Ext p' aug => fun P H => H p' aug
  |_ => tt
  end.


(** Morphisms of polygraphs **)

Record MAug {F F' : Type} {n :nat} (f : F -> F') (aug : Aug F n) (aug' : Aug F' n) :=
  mkMAug {
      ME: E aug -> E aug';
      Md : forall e x, d aug' (ME e, x) = f (d aug (e, x))
    }.

Arguments ME {_ _ _ _ _ aug'} _ _.
Arguments Md {_ _ _ _ _ aug'} _ _ _.
Arguments mkMAug {_ _ _ _ _ aug' } _ _. 

Notation "aug1 - f -- aug2" := (MAug f aug1 aug2) (at level 10).  


Definition FreeMA {F F' : Type} {n : nat} {aug : Aug F n} {aug' : Aug F' n}  {f : F -> F'} : aug - f -- aug' -> (FreeA aug -> FreeA aug').
Proof.
  intros Phi. 
  simple refine (Pushout_rect _ _ _).
  - intro xf. exact (inl (f xf)).
  - intros. simple refine (inr _).
    exact (ME Phi X.1, X.2).
  - intro x. simpl.
    simple refine ((f_equal inl (Md Phi x.1 x.2))^ @ _). 
    exact (incoh (ME Phi x.1, x.2)).
Defined.


Inductive MPol : forall n : nat, (Pol n) -> (Pol n) -> Type :=
| DiscM (T T' : Type) : (T -> T') -> MPol 0 (Disc T) (Disc T')
| ExtM (n : nat) (P P' : Pol n) (aug : Aug (Free P) (S n)) (aug' : Aug (Free P') (S n))
       (f : MPol n P P') (Mf : MAug (FreeM P P' f) aug aug') : MPol (S n) (Ext P aug) (Ext P' aug')
 fix FreeM {n : nat} (P P' : Pol n) (X : MPol n P P') : (Free P) -> (Free P') :=
  match X with
  |DiscM _ _ f => f
  |ExtM _ _ _ _ _ _ Mf => FreeMA Mf
  end.

Notation "P ~> Q" := (MPol _ P Q) (at level 10).
                                               
Arguments MPol {_} _ _.
Arguments DiscM {_ _} _.
Arguments ExtM {_ _ _ _ _} _ _.
Arguments FreeM {_ _ _} _.

(** As often with dependent types, destructors are not precis enough, so we define our own: one version for n=0, the other when n = S n' **)


Definition case2 (n : nat) (p0 p1 : Pol n)
           (P : forall n : nat, Pol n -> Pol n -> Type)
           (H0 : forall T0 T1, P 0 (Disc T0) (Disc T1))
           (HS : forall n p0 aug0 p1 aug1, P (S n) (Ext p0 aug0) (Ext p1 aug1)) :
  P n p0 p1 :=
  match p0 with
  |Disc T0 => (fun p1 => case0 _ (H0 T0) p1)
  |Ext p'0 aug'0 => (fun p1 => caseS' p1 _ (HS _ p'0 aug'0))
  end p1.

Definition caseM0 (T T' : Type)  (m : (Disc T) ~> (Disc T')):
  forall (P : MPol (Disc T) (Disc T') -> Type)
    (H : forall (f : T -> T'), P (DiscM f)),
    P m :=
  match m in @MPol n p p' return
        (case2 n p p'
               (fun _ p0 p0' => MPol p0 p0'-> Type)
               (fun t t'  => fun (f : MPol (Disc t) (Disc t'))
                          => forall (P : MPol (Disc t) (Disc t') -> Type) (H : forall f, P (DiscM f)), P f)
               (fun _ _ _ _ _ => (fun _ => unit))
               m)
  with
  | DiscM f => fun P H => H f
  | _ => tt
  end.

Definition caseMS' (n : nat) (p p' : Pol n) (aug : Aug (Free p) (S n)) (aug' : Aug (Free p') (S n))
           (m : (Ext p aug) ~> (Ext p' aug')) :
  forall (P : (Ext p aug) ~> (Ext p' aug') -> Type)
    (HS : forall  (f : p ~> p') (Mf : MAug (FreeM f) aug aug'), P (ExtM f Mf)),
    P m :=
  match m in @MPol n p p' return
        (case2 n p p'
               (fun _ p0 p0' => MPol p0 p0'-> Type)
               (fun _ _ => (fun _ => unit))
               (fun n0 p0 aug0 p'0 aug'0 => fun (m : MPol (Ext p0 aug0) (Ext p'0 aug'0))
                                         => forall P H, P m)
               m)
  with
  | ExtM f Mf => (fun P H => H f Mf)
  | _ => tt
  end.


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


Lemma FreeMA_inr {F F' : Type} {n : nat} {f : F -> F'} {aug : Aug F n} {aug' : Aug F' n}
      (G H : aug - f -- aug')
      (p : ME G = ME H )
      (q : forall e x,  (f_equal (fun W => d aug' (W e, x)) p) @ (Md H e x) = (Md G e x))
      (x : E aug × Ball n) :
  FreeMA G (inr x) = inr (ME G x.1, x.2).
Proof.
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

Definition eq_MPol (n : nat) (P P' : Pol n) (aug : Aug (Free P) (S n)) (aug' : Aug (Free P') (S n))
           (f f' : MPol P P') (MF : MAug (FreeM f) aug aug') (MF' : MAug (FreeM f') aug aug')
           (p : f = f') (q : eq_rect (fun W => MAug (FreeM W) aug aug')  MF p = MF') : ExtM f MF = ExtM f' MF'.
Proof.
  destruct p.
  destruct q.
  reflexivity.
Defined.

(**  Composition of morphisms of polygraphs **)


Definition ComposeMA {F F' F'' : Type} {n : nat} {f : F -> F'} {f' : F' -> F''} {aug : Aug F n} {aug' aug''} (G : MAug f aug aug') (G' : MAug f' aug' aug'') : MAug (compose f' f) aug aug''.
Proof.
  simple refine (mkMAug _ _).
  - exact (compose (ME G') (ME G)).
  - intros. unfold compose. exact ((Md G' (ME G e) x) @ (f_equal (fun W => f' W)  (Md G e x))).
Defined.


Definition FreeComposeMA {F F' F'' : Type} {n : nat} {f : F -> F'} {f' : F' -> F''} {aug : Aug F n} {aug' aug''} (G : MAug f aug aug') (G' : MAug f' aug' aug'') : FreeMA (ComposeMA G G') = compose (FreeMA G') (FreeMA G).
Proof.
  apply funext. 
  simple refine (Pushout_rect_dep _ _ _ _).
  - reflexivity.
  - reflexivity.
  - intro x. apply transport_lemma. simpl.
    rewrite concat_1p. unfold compose.
    rewrite ap_compose. unfold FreeMA. unfold compose.
    match goal with
    | |- _ = f_equal (Pushout_rect ?g1 ?g2 ?H) (incoh x) => refine (_ @ (Pushout_rect_compute_coh (f1 := d aug) (f2 := fun x => (x.1, (Faces n x.2))) (g1:= g1) (g2 := g2) (a := x))^)
    end.
    simpl. rewrite ap_concat.
    match goal with
    | |- f_equal ?F (f_equal (Pushout_rect ?g1 ?g2 ?H) (incoh x)) = _ => pose proof (Pushout_rect_compute_coh (f1 := d aug) (f2 := fun x => (x.1, (Faces n x.2))) (g1 := g1) (g2 := g2) (H := H) (a := x))
    end.
    match goal with
    | |- f_equal ?F ?u = ?v => refine (apap F H @ _); clear H
    end.
    rewrite ap_concat.
    rewrite concat_ap_V.
    match goal with
    | |- (f_equal ?a1 (f_equal inl ?a2))^ @ _ = _ => rewrite <- ap_compose
    end.
    unfold compose. simpl.
    match goal with
    | |- ?a1 @ f_equal (Pushout_rect ?g1 ?g2 ?H) (incoh ?y) = _ =>
      refine (f_equal (fun T => a1 @ T) (Pushout_rect_compute_coh (f1 := d aug') (f2 := fun x => (x.1, Faces n x.2)) (g1 := g1) (g2 := g2) (H := H)) @ _)
    end.
    simpl. rewrite concat_V.
    pose proof @ap_compose.
    unfold compose in H. rewrite <- H.
    now rewrite assoc.
Defined.


Fixpoint PolyComposeAndFree {n : nat} (p q r : Pol n) (G : p ~> q) (H : q ~> r) {struct n}:
  {Comp : p ~> r |
    FreeM Comp = compose (FreeM H) (FreeM G)}.
Proof.
  destruct n.
  - simple refine (mkDPair _ _); destruct p using case0; destruct q using case0; destruct r using case0;
      destruct H as [h] using (caseM0 _ _); destruct G as [g] using (caseM0 _ _).
    + econstructor. exact (compose h g).
    + exact 1.
  - simple refine (mkDPair _ _);
      destruct p as [p' Ep] using caseS';
      destruct q as [q' Eq] using caseS'; destruct r as [r' Er] using caseS';
      destruct G as [G' GAug] using (caseMS' _ _ _ _ _); destruct  H as [H' HAug] using (caseMS' _ _ _ _ _).
    + unshelve econstructor.
      * exact (fstd (PolyComposeAndFree _ _ _ _ G' H')).
      * refine (eq_rect (fun W => MAug W Ep Er) _ ((sndd (PolyComposeAndFree n p' q' r' G' H'))^)).
        exact (ComposeMA GAug HAug).
    + simpl. 
      simple refine (_ @ (FreeComposeMA _ _)).
      match goal with
      | |- ?f (eq_rect ?P ?p ?u) = _ => exact (image_transport P u p _)
      end.
Defined.

Notation ComposeM G H := (fstd (PolyComposeAndFree _ _ _ G H)).
Notation FreeComposeM G H := (sndd (PolyComposeAndFree _ _ _ G H)).

(** Identity morphism **)

Definition IdMA {n : nat} {T : Type} (aug : Aug T n)  : MAug (fun x => x) aug aug := mkMAug (fun x => x) (fun  _ _ => 1).

Definition FreeIdMA {n : nat} {T : Type} (aug : Aug T n) : FreeMA (IdMA aug) = (fun x => x).
Proof.
  apply funext.
  simple refine (eqMorphPushout _ _ _ ).
  - intro b1. simpl. reflexivity.
  - intro b2. simpl. destruct b2.  reflexivity.
  - simpl. intros [a a'].
    simple refine ( concat_1p _ @ _). 
    simple refine (ap_along_id _ @ _). 
    refine (_ @  Pushout_rect_compute_coh ^).
    exact ((concat_1p _)^).
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
        | |- MAug _ aug aug => simple refine (eq_rect (fun W => MAug W aug aug)  _ _)
        end.
        -- exact (fun x => x).
        -- simpl. exact (IdMA aug).
        -- exact ((sndd (IdAndFreeM n) p)^).
    + simpl. 
      simple refine ((image_transport _ _ _ _) @ (FreeIdMA _) ).
Defined.

Notation IdM p := (fstd IdAndFreeM p).

(** identity axioms: partial results **)


Definition left_id_MA {n : nat} {T T' : Type} {aug : Aug T n} {aug' : Aug T' n} {f : T -> T'} (F : aug - f -- aug') :
  ComposeMA F (IdMA aug') = F.
Proof.
  unfold ComposeMA. simpl.
  unshelve refine (eq_MA _ _ _ _).
  - reflexivity.
  - intros. simpl.
    simple refine (concat_1p _ @ _ @ (concat_1p _)^).
    exact ((ap_along_id _)^).
Defined.



Definition right_id_MA {n : nat} {T T' : Type} {aug : Aug T n} {aug' : Aug T' n} {f : T -> T'} (F : aug - f -- aug') :
  ComposeMA (IdMA aug) F = F.
Proof.
  reflexivity.
Defined.


(** associativity : partial results **)
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


Fixpoint ComposeM_assoc {n :nat} (p q r s : Pol n) (F : MPol p q) (G : MPol q r) (H : MPol r s) {struct n}:
  {c : ComposeM F (ComposeM G H) = ComposeM (ComposeM F G) H | f_equal FreeM c =
                                                               (FreeComposeM F (ComposeM G H))
                                                                 @ f_equal (fun W => compose W (FreeM F)) (FreeComposeM G H) 
                                                                 @ f_equal (fun W => compose (FreeM H) W) (FreeComposeM F G)^
                                                               @ (FreeComposeM (ComposeM F G) H)^}.
Proof.
Admitted.

