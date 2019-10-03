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

Variable (A : nat -> Type)
         (B : nat -> Type)
         (ι : forall n : nat, A n -> B n).
              

Inductive Pol : nat -> Type :=
|Disc : Type -> Pol 0
|Ext {n : nat} (P : Pol n) (E : Type) (d : E * A (S n) -> Free P) : Pol (S n)
fix Free {n : nat} (P : Pol n) : Type :=
  match P with
  | Disc A => A
  | Ext n0 _ E d => Pushout d (fun x => (fst x, ι _ (snd x)) : E * B (S n0))
  end.


Definition case0 (P : Pol 0 -> Type) (H : forall (T : Type), P (Disc T))  (p : Pol 0) : P p := 
  match p with
  |Disc T => H T
  |_ => tt
  end.

Notation "[ P ]*" := (Free P) : poly_scope.

Open Scope poly_scope.

Definition caseS' (n : nat) (p : Pol (S n)) :
  forall (P : Pol (S n) -> Type) (H : forall (p : Pol n) (E : Type) (d : E * A (S n) -> [p]* ), P (Ext p E d)), P p :=
  match p with
  |Ext p' E d  => fun P H => H p' E d
  |_ => tt
  end.



Definition tr (n : nat) : Pol (S n) -> Pol n.
Proof.
  intro P. destruct P using (caseS' n).
  exact P.
Defined.

Definition ooPol : Type := {P : forall n : nat, Pol n | forall n : nat, tr n (P (S n)) = P n}.



Definition inj {n : nat} (P : Pol n) (Q : Pol (S n)) (e : tr n Q = P) : [ P ]* -> [ Q ]*. 
Proof.
  intro.
  destruct Q using (caseS' _).
  apply inl. change [Q ]*. simpl in e. destruct e. exact X.
Defined.

Definition ootr (n :nat) (P : ooPol) : Pol n.
  destruct P.
  exact (fstd n).
Defined.

Module Export ooFreeType.

  Variable (P : ooPol).
  
  Private Inductive ooFree : Type :=
  | c : forall n : nat, [ootr n P]* -> ooFree.

  Lemma tr_coh : forall n : nat, tr n (ootr (S n) P) = ootr n P.
    intro n. destruct P. simpl. apply sndd.
  Defined.

  Axiom pathooFree : forall (n : nat) (x : [ootr n P]* ), c n x = c (S n) (inj _ _ (tr_coh _) x). 
                                
  Definition SuspensionInduction {T : Type} (iT : forall n : nat, [ootr n P]* -> T)                                           
             (f:  forall (n : nat) (x : [ootr n P]* ), iT n x = iT (S n) (inj _ _ (tr_coh _) x) )  (x : ooFree) : T :=
    match x with
    |c n x => iT n x
    end.

Section FreeMA_sec.
Context  {n : nat} {P P' : Pol n} {E E' : Type} {d : E * A (S n) -> [P]*} {d' : E' * A (S n) -> [P']* }
         (Φ : [P]*  -> [P']* )
         (ϕ : E -> E')
         (H : forall a, d' (ϕ (fst a), (snd a)) = Φ (d a)).

Definition FreeMA :  [Ext P E d]* -> [Ext P' E' d']*.
Proof.
  simple refine (Pushout_rect _ _ _).
  - intro xf. change _ with [P]* in xf. exact (inl (Φ xf)).
  - intros. simple refine (inr _).
    exact (ϕ (fst X), snd X ).
  - simpl. intro a. 
    simple refine ((ap inl (H a)^) @ _).
    exact (incoh (ϕ (fst a), snd a)).
Defined.                           

Definition FreeMA_compute  (a : E * A (S n)) :
  ap FreeMA (incoh a) = ap inl (H a)^ @ incoh (f1 := d') (ϕ (fst a), snd a).
Proof.
  refine Pushout_rect_compute_coh.
Defined.

End FreeMA_sec.

Definition H12  {n : nat} {P P' P'': Pol n} {E E' E'' : Type}
           {d : E * A (S n) -> [P]* } {d' : E' * A (S n) -> [P']* }
           {d'' : E'' * A (S n) -> [P'']* }
           (Φ1 : [P]*  -> [P']* ) (ϕ1 : E -> E') (H1 : forall a, d' (ϕ1 (fst a), (snd a)) = Φ1 (d a))
           (Φ2 : [P']*  -> [P'']* ) (ϕ2 : E' -> E'') (H2 : forall a, d'' (ϕ2 (fst a), (snd a)) = Φ2 (d' a)) :
  forall a, d'' (ϕ2 (ϕ1 (fst a)), snd a) = Φ2 (Φ1 (d a)).
Proof.
  intro a. refine  (H2 (ϕ1 (fst a), snd a) @ _).
  refine (ap Φ2 (H1 _)).
Defined.

Definition FreeComposeMA  {n : nat} {P P' P'': Pol n} {E E' E'' : Type}
           {d : E * A (S n) -> [P]* } {d' : E' * A (S n) -> [P']* }
           {d'' : E'' * A (S n) -> [P'']* }
           (Φ1 : [P]*  -> [P']* ) (ϕ1 : E -> E') (H1 : forall a, d' (ϕ1 (fst a), (snd a)) = Φ1 (d a))
           (Φ2 : [P']*  -> [P'']* ) (ϕ2 : E' -> E'') (H2 : forall a, d'' (ϕ2 (fst a), (snd a)) = Φ2 (d' a)) :
  FreeMA (Φ2 ∘ Φ1) (ϕ2 ∘ ϕ1) (H12 Φ1 ϕ1 H1 Φ2 ϕ2 H2) = (FreeMA Φ2 ϕ2 H2) ∘ (FreeMA Φ1 ϕ1 H1).
Proof.
   unfold compose. simpl. simple refine ( (composeCPushout _ _)^).
   - exact (fun x => (ϕ1 (fst x), snd x)).
   - simpl. intro a.  exact ((H1 a)^).
   - simpl. reflexivity.
   - intro a. simpl. refine (ap inl (H2 a)^ @ _). refine (incoh _).
   - simpl. apply FunExtDep. intro a.
     exact ((concat_p1 _)^).
   - simpl. apply FunExtDep. intros a.
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
| ExtM (n : nat) (P P' : Pol n) (E E' : Type) (d : E * A (S n) -> [P]* ) (d' : E' * A (S n) -> [P']* ) 
       (Φ : MPol n P P')
       (ϕ : E -> E')
       (H : forall a, d' (ϕ (fst a), (snd a)) = (FreeM P P' Φ) (d a)) : MPol (S n) (Ext P E d) (Ext P' E' d') 
fix FreeM {n : nat} (P P' : Pol n) (F : MPol n P P') : [P]* -> [P']* :=
  match F with
  |DiscM _ _ f => f
  |ExtM _ _ _ _ _ _ _ Φ ϕ H => FreeMA (FreeM _ _ Φ) ϕ H
  end.
                                               
Arguments MPol {_} _ _.
Arguments DiscM {_ _} _.
Arguments ExtM {_ _ _ _ _ _ _} _ _.
Arguments FreeM {_ _ _} _.



Definition case2 (n : nat) (p p' : Pol n)
           (P : forall n : nat, Pol n -> Pol n -> Type)
           (H0 : forall T T', P 0 (Disc T) (Disc T'))
           (HS : forall n p E d p' E' d', P (S n) (Ext p E d) (Ext p' E' d')) :
  P n p p' :=
  match p with
  |Disc T => (fun p' => case0 _ (H0 T) p')
  |Ext p0 E0 d0 => (fun p' => caseS' _ p' _ (HS _ p0 E0 d0))
  end p'.

  
Definition caseM0 (T T' : Type)  (m : MPol (Disc T) (Disc T')):
  forall (P : MPol (Disc T) (Disc T') -> Type)
    (H : forall (f : T -> T'), P (DiscM f)),
    P m :=
  match m in @MPol n p p' return
        (case2 n p p'
               (fun _ p0 p0' => MPol p0 p0'-> Type)
               (fun t t'  => fun (f : MPol (Disc t) (Disc t'))
                          => forall (P : MPol (Disc t) (Disc t') -> Type) (H : forall f, P (DiscM f)), P f)
               (fun _ _ _ _ _ _ _ => (fun _ => unit))
               m)
  with
  | DiscM f => fun P H => H f
  | _ => tt
  end.


Definition caseMS' (n : nat) (p p' : Pol n) (E E' : Type) (d : E * (A  (S n)) -> [p]* )
           (d' : E' * (A (S n)) -> [p']* )
           (m : MPol (Ext p E d) (Ext p' E' d')) :
  forall (P : MPol (Ext p E d) (Ext p' E' d') -> Type)
    (HS : forall  (Φ : MPol p p')
             (ϕ : E -> E')
             (H : forall a, d' (ϕ (fst a), (snd a)) = (FreeM Φ) (d a)) , P (ExtM Φ ϕ H)),
    P m.
  refine(
  match m in @MPol n p p' return
        (case2 n p p'
               (fun _ p0 p0' => MPol p0 p0'-> Type)
               (fun _ _ => (fun _ => unit))
               (fun n0 p0 E0 d0 p'0 E'0 d'0 => fun (m : MPol (Ext p0 E0 d0) (Ext p'0 E'0 d'0))
                                            => forall P H, P m)
               m)
  with
  | ExtM Φ ϕ Hf => _
  | _ => tt 
  end).
  exact (fun P H => H Φ ϕ Hf). Defined.
Print caseMS'.


Fixpoint PolyComposeAndFree {n : nat} (p q r : Pol n) (f : MPol p q) (g : MPol q r) {struct n}:
  {Comp : MPol p r |
    FreeM Comp = compose (FreeM g) (FreeM f)}.
Proof.
  destruct n.
  - simple refine (mkDPair _ _); destruct p using case0; destruct q using case0; destruct r using case0;
      destruct f as [f] using (caseM0 _ _); destruct g as [g] using (caseM0 _ _).
    + econstructor. exact (compose g f).
    + exact 1.
  - unshelve econstructor. 
    destruct p as [p' Ep dp] using (caseS' n).
      destruct q as [q' Eq dq] using (caseS' n). destruct r as [r' Er dr] using (caseS' n).
        destruct f as [f' ϕf Hf] using (caseMS' _ _ _ _ _ _ _). destruct  g as [g' ϕg Hg] using (caseMS' _ _ _ _ _ _ _).
    + unshelve econstructor.
      * exact (fstd (PolyComposeAndFree _ _ _ _ f' g')).
      * exact (compose ϕg ϕf).
      * intros.
        refine (Hg (ϕf (fst a), snd a) @ _).
        refine (ap (FreeM g') (Hf a) @ _).
        exact (ap (fun x => x (dp a)) (sndd (PolyComposeAndFree n p' q' r' f' g'))^).
    + simpl.
      destruct p as [p' Ep dp] using (caseS' n).
      destruct q as [q' Eq dq] using (caseS' n). destruct r as [r' Er dr] using (caseS' n).
      destruct f as [f' ϕf Hf] using (caseMS' _ _ _ _ _ _ _). destruct  g as [g' ϕg Hg] using (caseMS' _ _ _ _ _ _ _).
      simpl.
      apply funext.
      unshelve refine (Pushout_rect_dep _ _ _ _).
      * intros. change _ with [p']* in b1.
        unfold FreeMA. simpl. unfold compose. simpl.
        exact (ap (fun x => inl (x b1)) (sndd (PolyComposeAndFree _ _ _ _ _ _))).
      * reflexivity.
      * intro. simpl. 
        match goal with
        | |- transport (fun x => ?F x = compose ?G1 ?G2 x) (incoh a) ?p = 1 => refine (transport_lemma (incoh a) F (compose G1 G2) p 1 _)
        end.
        refine ( _ @ (concat_p1 _)^).
        refine ( _ @ (Pushout_rect_compute_coh (a := a) ^)).
        match goal with
        | |- ?p @ ap (?f ∘ ?g)  (incoh a) = _ => refine (ap (fun X => p @ X) (ap_compose g f (incoh a)) @ _)
        end.
        unfold compose. Set Printing Universes.
        match goal with
        | |- ?p @ ap ?F ?u = _ =>
          match type of u with
            |?x = ?y => refine (ap (fun X => p @ ap (x := x) (y := y) F X) _  @ _)
          end
        end. (** This is a problem... **)
        match ap_compose
        refine (_ @  Pushout_rect_compute_coh^).
        end.

        rewrite Pushout_rect_compute_coh.
                                                                                                
        apply transport_lemma.
        match goal with
        | |- FreeMA
        
      simple refine (_ @ (FreeComposeMA _ _)).
      match goal with
      | |- ?f (transport ?P ?p ?u) = _ => exact (image_transport P p u _)
      end.
Defined.                   
                             
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



