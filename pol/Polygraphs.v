Require Import Paths.
Require Import HIT.

                     

(*
(* Type equipped with additional cells *)
Inductive Augmentation (F : Type) (n : nat) : Type :=
  Cells (E : Type) (d : E ->  Sphere n -> F) : Augmentation F n.

Arguments Cells {F} {n} (E) (d).

Definition FreeType {F : Type} {n : nat} (X : @Augmentation F n) : Type :=
  match X with
  | Cells E d => CPushout d (fun (e : E) (x : Sphere n) => (e, Faces n x))
  end.

 *)

Inductive  Aug (F : Type) (n : nat) : Type :=
  mkAug (E : Type)  (d : E * Sphere n -> F) : Aug F n.


Arguments mkAug {_ _} _ _.

Definition FreeA {F : Type} {n : nat} (aug : Aug F n) : Type :=
  match aug with
  | mkAug E d =>  Pushout d (fun x  => (fst x, Faces n (snd x)) : E * Ball n)
  end.

Inductive Pol : nat -> Type :=
|Disc : Type -> Pol 0
|Ext {n : nat} (P : Pol n) (aug : Aug (Free P) (S n)) : Pol (S n)
fix Free {n : nat} (P : Pol n) : Type :=
       match P with
       | Disc A => A
       | Ext _ _ aug => FreeA aug
       end.

Opaque Free.

Notation "[ P ]*" := (Free P).

Definition case0 (P : Pol 0 -> Type) (H : forall (T : Type), P (Disc T))  (p : Pol 0) : P p := 
  match p with
  |Disc T => H T
  |_ => tt
  end.

Definition caseS' (n : nat) (p : Pol (S n)) :
  forall (P : Pol (S n) -> Type) (H : forall (p : Pol n) (aug : Aug [ p ]* (S n)), P (Ext p aug)), P p :=
  match p with
  |Ext p' aug => fun P H => H p' aug
  |_ => tt
  end.

(** Definition of the Morphisms of polygraphs **)
           
Inductive MAug {F F' : Type} {n :nat} (f : F -> F') : Aug F n -> Aug F' n -> Type :=
  mkMAug E d E' d' (MCells: E -> E') (H : forall e x, d' (MCells e, x) = f (d (e, x))) : MAug f (mkAug E d) (mkAug E' d').

Arguments mkMAug {_ _ _ _ _ _ _ _ } _ _. 

Notation "aug1 - f -- aug2" := (MAug f aug1 aug2) (at level 10).  


Definition caseMAug {F F' : Type} {n :nat} (f : F -> F') E d E' d' (Phi : (mkAug E d) - f -- (mkAug E' d')) :
  forall (P : (mkAug E d) - f --  (mkAug E' d') -> Type)
    (H : forall MCells HCells, P (@mkMAug F F' n f E d E' d' MCells HCells)),
    P Phi :=
  match Phi with
  |mkMAug MCells HCells => (fun P H => H MCells HCells)
  end.

Arguments caseMAug {_ _ _ _ _ _ _ _} _.


Definition FreeMA {F F' : Type} {n : nat} {aug : Aug F n} {aug' : Aug F' n}  {f : F -> F'} : aug - f -- aug' -> (FreeA aug -> FreeA aug').
Proof.
  intros Phi. destruct aug as [E d], aug' as [E' d'].
  simple refine (Pushout_rect _ _ _).
  - intro xf. exact (inl (f xf)).
  - intros. simple refine (inr _).
    destruct Phi as [PhiE Phid] using caseMAug.
    exact (PhiE (fst X), snd X ).
  - intros [a a']. simpl.
    destruct Phi as [PhiE Phid] using caseMAug. 
    simple refine ((ap inl (Phid a a')^) @ _).
    exact (incoh (PhiE a,a')).
Defined.


Definition ComposeMA {F F' F'' : Type} {n : nat} {f : F -> F'} {f' : F' -> F''} {aug : Aug F n} {aug' aug''} (G : MAug f aug aug') (G' : MAug f' aug' aug'') : MAug (compose f' f) aug aug''.
Proof.
  destruct aug as [E d]. destruct aug' as [E' d']. destruct aug'' as [E'' d''].
  destruct G as [GE Gd] using caseMAug. destruct G' as [GE' Gd'] using caseMAug.
  simple refine (mkMAug _ _).
  -  exact (compose GE' GE).
  - simpl. intros. unfold compose. exact ((Gd' (GE e) x) @ (ap (fun W => f' W)  (Gd e x))).
Defined.


Definition FreeComposeMA {F F' F'' : Type} {n : nat} {f : F -> F'} {f' : F' -> F''} {aug : Aug F n} {aug' aug''} (G : MAug f aug aug') (G' : MAug f' aug' aug'') : FreeMA (ComposeMA G G') = compose (FreeMA G') (FreeMA G).
Proof.
   destruct aug as [E d]. destruct aug' as [E' d']. destruct aug'' as [E'' d''].
   destruct G as [GE Gd] using caseMAug. destruct G' as [GE' Gd'] using caseMAug.
   simpl. 
   unfold compose. simpl. simple refine ( (composeCPushout _ _)^).
   - exact (fun x => (GE (fst x), snd x)).
   - simpl. intros [a a'].  exact ((Gd a a')^).
   - simpl. reflexivity.
   - simpl. apply FunExtDep. intros [a a'].
     exact ((concat_p1 _)^).
   - simpl. apply FunExtDep. intros [a a']. 
     simple refine (_ @ (concat_p1 _)^).
     match goal with
     | |- _ @ ?p = _ =>
       simple refine ((ap (fun W => W @ p) (concat_ap_V _ _)) @  _);
         simple refine ((ap (fun W => W ^ @ p) (ap_concat _ _ _)) @ _);
         simple refine ((ap (fun W => W @ p) (concat_V _ _)) @ _);
         simple refine ((assoc _ _ _)^ @ _ )
     end.
     match goal with
     | |- (ap ?f (ap ?g ?p1)) ^ @ ?p2 = _ =>
       simple refine ((ap (fun W => W^ @ p2) (ap_compose _ _ _)^) @ _)
     end.
     unfold compose.
     match goal with
     | |- _ = _ @ ?p =>
       refine (_ @ ap (fun W => W @ p) (concat_ap_V _ _)^)
     end.
     match goal with
     | |- _ = ?p @ (_ @ ?q) =>
       exact (ap (fun W => p @ (W @ q)) (concat_ap_V inl _)^)
     end.
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

Print caseS'.


Definition case2 (n : nat) (p p' : Pol n)
           (P : forall n : nat, Pol n -> Pol n -> Type)
           (H0 : forall T T', P 0 (Disc T) (Disc T'))
           (HS : forall n p aug p' aug', P (S n) (Ext p aug) (Ext p' aug')) :
  P n p p' :=
  match p with
  |Disc T => (fun p' => case0 _ (H0 T) p')
  |Ext p0 aug0 => (fun p' => caseS' _ p' _ (HS _ p0 aug0))
  end p'.

Check case2.

  
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

Definition caseMS' (n : nat) (p p' : Pol n) (aug : Aug [p]* (S n)) (aug' : Aug [p']* (S n))
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
      destruct p as [p' Ep] using (caseS' n);
      destruct q as [q' Eq] using (caseS' n); destruct r as [r' Er] using (caseS' n);
      destruct G as [G' GAug] using (caseMS' _ _ _ _ _); destruct  H as [H' HAug] using (caseMS' _ _ _ _ _).
    + unshelve econstructor.
      * exact (fstd (PolyComposeAndFree _ _ _ _ G' H')).
      * refine (transport (fun W => MAug W Ep Er) ((sndd (PolyComposeAndFree n p' q' r' G' H'))^) _).
        exact (ComposeMA GAug HAug).
    + simpl.
      simple refine (_ @ (FreeComposeMA _ _)).
      match goal with
      | |- ?f (transport ?P ?p ?u) = _ => exact (image_transport P p u _)
      end.
Defined.

Notation ComposeM G H := (fstd (PolyComposeAndFree _ _ _ G H)).
Notation FreeComposeM G H := (sndd (PolyComposeAndFree _ _ _ G H)).




