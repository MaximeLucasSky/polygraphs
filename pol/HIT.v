Require Import Paths.

Module Export Suspension.
  Private Inductive Suspension (A : Type) : Type :=
    NN : Suspension A
  | SS : Suspension A.
  
  Axiom pathSuspension : forall {A : Type} , A -> (NN A) = (SS A).
   
  Definition SuspensionInduction {A : Type} {B : Type} (vn : B) (vs : B) (f: A -> (vn = vs)) (x : Suspension A) : B :=
    match x with
    |NN _ => (fun _ => vn)
    |SS _ => (fun _ => vs)
    end f .

  Axiom SuspensionInduction_path :
    forall A B (vn vs : B) f (a : A),
      ap (SuspensionInduction vn vs f) (pathSuspension a) = (f a).
  
  Definition SuspensionInductionDependant {A : Type}:
    forall (B : Suspension A -> Type)
           (vn : B (NN A)) (vs : B (SS A))
           (f : forall a : A,  (pathSuspension a) # vn = vs )
           (x : Suspension A), B x := fun B vn vs f x => 
    match x with
    |NN _ => (fun _ => vn)
    |SS _ => (fun _ => vs)
    end f .


  Axiom SuspensionInductionDependant_path :
    forall A B (vn : B (NN A)) (vs : B (SS A)) f (a : A),
      apd (SuspensionInductionDependant B vn vs f) (pathSuspension a) = (f a).
End Suspension.


Definition Interval := Suspension unit.


      
Definition eqMorph (A T: Type) (F G : Suspension A -> T)
           (HN: F (NN A) = G (NN A))
           (HS: F (SS A) = G (SS A))
           (Heq : forall a : A,   HN @ (ap G (pathSuspension a)) = (ap F (pathSuspension a)) @ HS )
  : forall x : Suspension A, F x = G x.
Proof.
  unshelve eapply (@SuspensionInductionDependant A).
  - exact HN.
  - exact HS.
  - intro. apply transport_lemma. exact (Heq a). 
Defined.


Definition SuspensionMap {A B : Type} (f : A -> B) (x : Suspension A) : Suspension B :=
  SuspensionInduction (NN B) (SS B) (fun a => pathSuspension (f a)) x.

(*Ici, Sphere n est le bord de Ball n, au lieu du bord de  Ball n+1 traditionnellement *)
Fixpoint Sphere (n : nat) : Type :=
  match n with
  |0 => False
  |S m => Suspension (Sphere m)
  end.


Fixpoint Ball (n : nat) : Type :=
  match n with
  |0 => True
  |Datatypes.S m => Suspension  (Ball m)
  end.

Fixpoint Faces (n : nat) : (Sphere n) -> (Ball n) :=
  match n with
  |0 => (False_rect True)
  |S m => SuspensionMap (Faces m)
  end.


Fixpoint Source (n : nat) : (Ball n) -> (Sphere (S n)) :=
  match n with
  |0 => (fun _ => NN _)
  |S m => SuspensionMap (Source m)
  end.
Fixpoint Target (n : nat) : (Ball n) -> (Sphere (S n)) :=
  match n with
  |0 => (fun _ => SS _)
  |S m => SuspensionMap (Source m)
  end.


Arguments Sphere n : simpl nomatch.
Arguments Ball n : simpl nomatch.
Arguments Faces n : simpl nomatch.
Arguments Source n : simpl nomatch.
Arguments Target n : simpl nomatch.
(*
Notation nSpheres n T := (Sphere n -> T).
Notation nBalls n T := (Ball n -> T). *)
Definition nFaces (n : nat) (T : Type) : (Ball n -> T) -> (Sphere n -> T) :=
  fun x => (compose x (Faces n)).

Module Export Pushout.
  Private Inductive Pushout {A B1 B2 : Type} (f1 : A -> B1) (f2: A -> B2) : Type :=
  |inl : B1 -> Pushout f1 f2
  |inr : B2 -> Pushout f1 f2.

  Arguments inl {_ _ _ _ _} _.
  Arguments inr {_ _ _ _ _} _.
       
  Axiom incoh : forall A B1 B2 : Type, forall f1 : A -> B1, forall f2: A -> B2,  forall a:A, @inl _ _ _ f1 f2 (f1 a) = @inr _ _ _ f1 f2 (f2 a).

  Arguments incoh {_ _ _ _ _} _.

  Definition Pushout_rect {A B1 B2 : Type} {f1 : A -> B1} {f2 : A -> B2}
             {B : Type} (g1 : B1 -> B) (g2 : B2 -> B)
             (H : forall a : A, (g1 (f1 a) = g2 (f2 a))) (x : Pushout f1 f2) : B :=
    match x with
    |inl  b1 => (fun _ => g1 b1) 
    |inr  b2 => (fun _ => g2 b2)
    end H.

  Axiom Pushout_rect_compute_coh : forall {A B1 B2} {f1 : A -> B1} {f2 : A -> B2} {B} {g1 : B1 -> B} {g2 : B2 -> B} {H a},
      ap (@Pushout_rect _ _ _ f1 f2 _ g1 g2 H) (incoh a) = H a.

  
  Definition Pushout_rect_dep {A B1 B2 : Type} {f1 : A  -> B1} {f2 : A -> B2} :
    forall (P : Pushout f1 f2 -> Type)
           (g1 : forall b1 : B1, P (inl b1))
           (g2 : forall b2 : B2, P (inr b2))
           (H : forall a, (incoh a) # g1 (f1 a) = g2 (f2 a))
           (x : Pushout f1 f2), P x :=
    (fun P g1 g2 H x =>
       match x with
       |inl b1 => (fun _ => g1 b1)
       |inr b2 => (fun _ => g2 b2)
       end H
    ).
 
  Axiom Pushout_rect_dep_compute :
    forall {A B1 B2 : Type} {f1 : A -> B1} {f2 : A -> B2}
           {P : Pushout f1 f2 -> Type}
           {g1 : forall b1 : B1, P (inl  b1)}
           {g2 : forall b2 : B2, P (inr  b2)}
           {H : forall a, (incoh a) # g1 (f1 a) = g2 (f2 a)}
           {a},
      apd (Pushout_rect_dep P g1 g2 H) (incoh a) = H a.
End Pushout.

Lemma Pushout_rect_compute_inl : forall {A B1 B2 : Type}, forall {f1 : A -> B1}, forall {f2 : A -> B2},
          forall {B} {g1 : B1 -> B} {g2 : B2 -> B} {H :  forall a: A,  g1 (f1 a ) = g2 (f2 a )} {b1 b'1 : B1} {p : b1 = b'1} ,
            ap (Pushout_rect g1 g2 H) (ap inl p) = ap g1 p.
Proof.
  destruct p.
  reflexivity.
Defined.

Lemma Pushout_rect_compute_inr : forall {A B1 B2 : Type}, forall {f1 : A  -> B1}, forall {f2 : A  -> B2},
          forall {B} {g1 : B1 -> B} {g2 : B2 -> B} {H :  forall a: A, g1 (f1 a) = g2 (f2 a)} {b2 b'2 : B2} {p : b2 = b'2} ,
            ap (Pushout_rect g1 g2 H) (ap inr p) = ap g2 p.
Proof.
  destruct p.
  reflexivity.
Defined.
                

Definition eqMorphPushout {A B1 B2 T: Type} {f1 : A -> B1} {f2 : A -> B2} {F G : Pushout f1 f2 -> T}
           (H1: forall b1 : B1, F (inl b1) = G (inl b1))
           (H2: forall b2 : B2, F (inr b2) = G (inr b2))
           (Heq : forall (a : A),  H1 (f1 a) @ (ap G (incoh a)) = (ap F (incoh a)) @ H2 (f2 a) )
  : forall x : Pushout f1 f2, F x = G x.
Proof.
  simple refine  (Pushout_rect_dep _ _ _ _).
  - exact H1.
  - exact H2.
  - intros. simple refine (transport_lemma _ _ _ _ _ _). exact (Heq a). 
Defined.




Lemma composeCPushout {A B1 B2} {X Y1 Y2} {Z}
      {f1 : A -> B1} {f2 : A -> B2} {g1 : X -> Y1} {g2 : X -> Y2}
      {h1 : B1 -> Y1} {h2 : B2 -> Y2}  {h : A -> X}
      {Hh1 : forall a, h1 (f1 a) = g1 (h a)} {Hh2 : forall a, g2 (h a) = h2 (f2 a)}
      {i1 : Y1 -> Z} {i2 : Y2 -> Z} {Hi : forall x, i1 (g1 x) = i2 (g2 x)}
      {H1 H2}
      (HH1: H1 = (fun a => (ap inl (Hh1 a)) @ (incoh (h a)) @ (ap inr (Hh2 a))))
      (HH2 : H2 =  (fun a => (ap i1 (Hh1 a)) @ (Hi (h a)) @ (ap i2 (Hh2 a)))):
  compose (Pushout_rect i1 i2 Hi)
          (Pushout_rect (fun x => inl (h1 x))
                         (fun x => inr (h2 x))
                         H1)
  = (Pushout_rect (fun x => i1 (h1 x))
                   (fun x => i2 (h2 x))
                   H2).
Proof.
  match goal with
  | |- compose ?arg1 (Pushout_rect ?arg2 ?arg3 _)  = _ =>
    simple refine (concat (ap (fun W => compose arg1 (Pushout_rect arg2 arg3 W)) HH1) _)
  end.
  match goal with
  | |- _ = Pushout_rect ?arg1 ?arg2 _ =>
    simple refine (concat _ (ap (fun W => Pushout_rect arg1 arg2 W) HH2^))
  end.
  apply funext.
  simple refine (eqMorphPushout _ _ _).
  - reflexivity.
  - reflexivity.
  - intros. simpl.
    simple refine ((concat_1p _) @ _).
    simple refine (_ @ (concat_p1 _)^).
    simple refine (Pushout_rect_compute_coh @ _).
    match goal with
    | |- _ = ap (compose ?G ?F) ?p => simple refine (concat _ (ap_compose F G p)^)
    end. unfold compose.
    match goal with
    | |- _ = ap ?f _ => simple refine (concat _ (ap (fun W => ap f W) Pushout_rect_compute_coh^))
    end.
    simple refine (concat _ (ap_concat _ _ _)^).
    match goal with
    | |- _ = _ @ ?p => simple refine (concat _ (ap (fun W => W @ p) (ap_concat _ _ _)^))
    end.
    match goal with
    | |- _ = ?p1 @ _ @ ?p2 => simple refine (concat _ (ap (fun W => p1 @ W @ p2) Pushout_rect_compute_coh^))
    end.
    match goal with
    | |- _ = ?p1 @ _ => simple refine (concat _ (ap (fun W => p1 @ W) Pushout_rect_compute_inr^))
    end.
    match goal with
    | |- _ = (_ @ ?p1) @ ?p2 => exact (ap (fun W => (W @ p1) @ p2) Pushout_rect_compute_inl^)
    end.
Defined.