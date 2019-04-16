Require Import Paths.
Require Import HIT.
Require Import Polygraphs.

(* Morphism of Polygraphs *)

(*
Lemma CPush_of_inl {F F' : Type} {E E' : Type} {n : nat} (d : E -> Sphere n -> F) (d' : E' -> Sphere n -> F')
      (f : F -> F') (g : E -> E') (HG : forall (e : E) (s : Sphere n), f (d e s) = d' (g e) s)
      {x x' : F} (p : x = x') :
  ap (@MorphFreeType _ _ _ _ (Cells E d) (Cells E' d') (existT _ g HG)) (ap (inl _ _) p) = ap (inl _ _) (ap f p).
Proof.
  destruct p. reflexivity.
Defined.
 *)


Inductive MAug {F F' : Type} {n :nat} (f : F -> F') : Aug F n -> Aug F' n -> Type :=
  mkMAug E d E' d' (MCells: E -> E') (H : forall e x, d' (MCells e, x) = f (d (e, x))) : MAug f (mkAug E d) (mkAug E' d').

(* Definition  MAug {F F' : Type}  {n : nat} (f : F -> F') (aug : Aug F n) (aug' : Aug F' n) : Type := *)
(*   match aug, aug' with *)
(*   |mkAug E d, mkAug E' d' => {MCells : E -> E' | forall e x, d' (MCells e) x = f (d e x)} *)
(*   end. *)

(* Definition MCells *)

(* Notation  MCells f := fst ({_ _ _ _ _ _} _. *)
(* Arguments Md {_ _ _ _ _ _} _ _ _. *)
 Arguments mkMAug {_ _ _ _ _ _ _ _ } _ _. 

Definition caseMAug {F F' : Type} {n :nat} (f : F -> F') E d E' d' (Phi : MAug f (mkAug E d) (mkAug E' d')) :
  forall (P : MAug f (mkAug E d) (mkAug E' d') -> Type)
    (H : forall MCells HCells, P (@mkMAug F F' n f E d E' d' MCells HCells)),
    P Phi :=
  match Phi with
  |mkMAug MCells HCells => (fun P H => H MCells HCells)
  end.

Arguments caseMAug {_ _ _ _ _ _ _ _} _.



Definition FreeMA {F F' : Type} {n : nat} {aug : Aug F n} {aug' : Aug F' n}  {f : F -> F'} : MAug f aug aug' -> (FreeA aug -> FreeA aug').
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

  
Definition caseM0 (T T' : Type)  (m : MPol (Disc T) (Disc T')):
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
           (m : MPol (Ext p aug) (Ext p' aug')) :
  forall (P : MPol (Ext p aug) (Ext p' aug') -> Type)
    (HS : forall  (f : MPol p p') (Mf : MAug (FreeM f) aug aug'), P (ExtM f Mf)),
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

  



Fixpoint PolyComposeAndFree {n : nat} (p q r : Pol n) (G : MPol p q) (H : MPol q r) {struct n}:
  {Comp : MPol p r |
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