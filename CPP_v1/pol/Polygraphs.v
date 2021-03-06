Require Import Basics.
Require Import Paths.
Require Import HIT.

         
Set Primitive Projections.


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




(** Definition of the Morphisms of polygraphs **)

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


(** This defines the composition of morphisms of polygraphs **)

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

