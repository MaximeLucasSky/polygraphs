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

Definition case0 (P : Pol 0 -> Type) (H : forall (T : Type), P (Disc T))  (p : Pol 0) : P p := 
  match p with
  |Disc T => H T
  |_ => tt
  end.

Definition caseS' (n : nat) (p : Pol (S n)) :
  forall (P : Pol (S n) -> Type) (H : forall (p : Pol n) (aug : Aug (Free p) (S n)), P (Ext p aug)), P p :=
  match p with
  |Ext p' aug => fun P H => H p' aug
  |_ => tt
  end.
                             
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



