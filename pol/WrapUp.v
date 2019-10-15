Require Import Paths.
Require Import HIT.
Require Import Polygraphs.
Require Import PolyMorphs.
Require Import Adjunction.


Definition Counit_inject (n : nat) (T : Type) : 
  compose  (CounitA (S n) (Counit T n)) (injectPol (Forget T n) (ForgetA (Counit T n) (S n)))
           = (Counit T n).
Proof.
  destruct n.
  - simpl. exact 1.
  - simpl.
    unfold compose. apply funext. simple refine (eqMorphPushout _ _ _).
    + intro b1. reflexivity.
    + intro b2. simpl. reflexivity.
    + intros [a a']. simpl. exact ((concat_p1 _)^).
Defined.

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
    match goal with
    | |- ?p @ ap ?f (?q @ ?r) = _ => simple refine (ap (fun W => p @ W) (ap_concat f q r) @ _)
    end.
    match goal with
    | |- ?p @ (?q @ ap ?f (ap ?g ?r)) = _ => exact (ap (fun W => p @ (q @ W)) (ap_compose g f r)^ @ (assoc _ _ _))
    end.
Defined.

Lemma forall_eq_rect {A : Type} {B : A -> Type} (f : forall a : A, B a) (P : forall g : (forall a : A, B a),  ((forall a : A, f a = g a)  -> Type))
      (H : P f (fun a => 1)) g p : P g p.
Proof.
  exact (forall_eq_destruct f (fun G => P (fstd G) (sndd G)) H (mkDPair g p)).
Defined.

Lemma forall_eq_destruct {A : Type} {B : A -> Type} (f g h : forall a : A, B a) (p : forall a : A, f a = g a) (q : forall a : A, g a = h a) :
  FunExtDep (fun a => p a @ q a) = FunExtDep p @ FunExtDep q.
Proof.
  simple refine (forall_eq_rect _ (fun h (q : forall a : A, g a = h a) =>  FunExtDep (fun a : A => p a @ q a) = FunExtDep p @ FunExtDep q) _ _ q).
  simpl.
  simple refine (ap (fun W => FunExtDep W) (FunExtDep (fun a : A => concat_p1 (p a))) @ _).
  simple refine (_ @ ap (fun W => FunExtDep p @ W) (FunExtDep_refl)^).
  exact ((concat_p1 _)^).
Defined.

Lemma ap_FreecomposeMA_inl {n :nat}  {F1 F2 F3 : Type} {f1 : F1 -> F2} {f2 : F2 -> F3}
         {aug1 : Aug F1 n} {aug2 : Aug F2 n} {aug3 : Aug F3 n} 
         (G1 : MAug f1 aug1 aug2) (G2 : MAug f2 aug2 aug3) (x : F1) :
  ap (fun T => T (inl x)) (FreeComposeMA G1 G2) = 1.
Proof.
  simpl.
  unfold FreeComposeMA. rewrite funextcompute. reflexivity.
Defined.


Lemma ap_FreecomposeMA_inr {n :nat}  {F1 F2 F3 : Type} {f1 : F1 -> F2} {f2 : F2 -> F3}
         {aug1 : Aug F1 n} {aug2 : Aug F2 n} {aug3 : Aug F3 n} 
         (G1 : MAug f1 aug1 aug2) (G2 : MAug f2 aug2 aug3) (x : (E aug1) × Ball n) :
  ap (fun T => T (inr x)) (FreeComposeMA G1 G2) = 1.
Proof.
  simpl.
  unfold FreeComposeMA. rewrite funextcompute. reflexivity.
Defined.


(* Section Foo. *)
(*   Variables (T T': Type) (f g : T -> T') (A B : f = g) (a b : T) (p : a = b) (Ha : ap (fun h => h a) A = ap (fun h => h a) B). *)
  
(*   Lemma toto  : ap (fun h => h b) A = ap (fun h => h b) B. *)
(*     refine (transport ( *)
(*     . *)
    

Definition square  {T T' : Type} {a b : T} {f g : T -> T'} (e : a = b) (p : f = g) : 
  ap (fun x => x a) p @ ap (fun x => g x) e = ap (fun x => f x) e @ ap (fun x => x b) p :> (f a = g b).
Proof.
  destruct e. simpl. exact (concat_p1 _).
Defined.

Lemma transport_lemma_dep
      {T T': Type} {a b : T} {f g : T -> T'} (e : a = b) (p q : f = g) (Ha : ap (fun x => x a) p = ap (fun x => x a) q)
      (Hb : ap (fun x => x b) p = ap (fun x => x b) q) :
  ap (fun r => r @ (ap (fun x => g x) e)) Ha @ (square e q) = (square e p) @ ap (fun r => (ap (fun x => f x) e) @ r) Hb
  -> transport (fun x => (ap (fun h => h x) p = ap (fun h => h x) q)) e Ha = Hb :> (_ = _ :> (f b = g b)).
Proof.
  intro.
  destruct e.
  destruct p.
  simpl  in *. 
  refine (_ @ H @ _).
  - rewrite <- Ha. reflexivity.
  - apply ap_id.
Defined.

Lemma ap_at {T: Type} {x y z: T} {e1 e2 e3: x = y} (p : y = z) (q1: e1 = e2) (q2 : e2 = e3) :
  ap (fun r => r @ p) (q1 @ q2) = (ap (fun r => r @ p) q1) @ (ap (fun r => r @ p) q2).
Proof.
  destruct q1. reflexivity.
Defined.

Lemma VV {T : Type} {x y : T} (p : x = y) : p^^ = p.
  now destruct p.
Defined.

Lemma Free_composeMA_assoc {n :nat}  {F1 F2 F3 F4 : Type} {f1 : F1 -> F2} {f2 : F2 -> F3} {f3 : F3 -> F4}
         {aug1 : Aug F1 n} {aug2 : Aug F2 n} {aug3 : Aug F3 n} {aug4 : Aug F4 n}
         (G1 : MAug f1 aug1 aug2) (G2 : MAug f2 aug2 aug3) (G3 : MAug f3 aug3 aug4):
  ap FreeMA (ComposeMA_assoc G1 G2 G3) = (FreeComposeMA G1 (ComposeMA G2 G3))
                                           @ (ap (fun W => compose W (FreeMA G1)) (FreeComposeMA G2 G3) 
                                           @ (ap (fun W => compose (FreeMA G3) W) (FreeComposeMA G1 G2)^
                                         @ (FreeComposeMA (ComposeMA G1 G2) G3)^)) .
Proof.
  apply eq_fun.
  unshelve refine (Pushout_rect_dep _ _ _ _ ).
  - intro x.
    refine ((ap_compose FreeMA _ (ComposeMA_assoc G1 G2 G3))^ @ _).  simpl.
    refine (ap_constant _ _ @ _).
    match goal with
    | |- 1 = ap ?f (?p1 @ (?p2 @ (?p3 @ ?p4))) => refine (_ @ (ap_concat _ _ _)^);
                                                  refine (_ @ ap (fun T => (ap f p1) @ T) (ap_concat f p2 (p3 @ p4))^);
                                                  refine (_ @ ap (fun T => (ap f p1) @ ((ap f p2) @ T)) (ap_concat f p3 p4)^)
    end.
    unfold compose in *.
    match goal with
    | |- 1 = ?a1 @ (ap ?f (ap ?g ?h) @ (?a2  @ ?a3)) => refine (_ @ ap (fun T => a1 @ (T @ (a2 @ a3))) (ap_compose g f h))
    end.
    cbn.
    match goal with
    | |- 1 =  ?a1 @ (?a2 @  (ap ?f (ap ?g ?h) @ ?a3)) => refine (_ @ ap (fun T => a1 @ (a2 @ (T @ a3))) (ap_compose g f h))
    end.
    match goal with
    | |- 1 = ?q1 @ (?q2 @ (ap ?f ?p1^ @ ap ?g ?p2^)) => refine (_ @ ap (fun T => q1 @ (q2 @ (ap f p1^ @ T))) (concat_ap_V g p2)^);
                                                   refine (_ @ ap (fun T => q1 @ (q2 @ (T @ (ap g p2)^))) (concat_ap_V f p1)^)
    end.
    match goal with
    | |- 1 = (ap _ (FreeComposeMA ?G1 ?G2)) @ ?a1 =>  refine (_ @ ap (fun T => T @ a1) (ap_FreecomposeMA_inl G1 G2 x)^)
    end. simpl.
    match goal with
    | |- 1 = (ap _ (FreeComposeMA ?G1 ?G2)) @ ?a1 =>  refine (_ @ ap (fun T => T @ a1) (ap_FreecomposeMA_inl G1 G2 (f1 x))^)
    end. simpl.
    match goal with
      |- 1 = (ap _ ?q)^ @ ?p=> refine (_ @ ap (fun T => T^ @ p) (ap_compose (fun x0 => x0 (inl x)) (FreeMA G3) q)^)
    end.
    match goal with
    | |- 1 = (ap ?a2 (ap _ (FreeComposeMA ?G1 ?G2))) ^ @ ?a1 =>  refine (_ @ ap (fun T => (ap a2 T) ^ @ a1) (ap_FreecomposeMA_inl G1 G2 x)^)
    end. simpl. 
    match goal with
    | |- 1 = (ap _ (FreeComposeMA ?G1 ?G2))^ =>  exact ( ap (fun T => T^) (ap_FreecomposeMA_inl G1 G2 x)^)
    end. 
  - intro b.
    refine ((ap_compose FreeMA _ (ComposeMA_assoc G1 G2 G3))^ @ _). 
    match goal with
    | |- _ = ap ?f (?p1 @ (?p2 @ (?p3 @ ?p4))) => refine (_ @ (ap_concat f p1 ( p2 @ (p3 @ p4)))^);
                                                  refine (_ @ ap (fun T => (ap f p1) @ T) (ap_concat f p2 (p3 @ p4))^);
                                                  refine (_ @ ap (fun T => (ap f p1) @ ((ap f p2) @ T)) (ap_concat f p3 p4)^)
    end. refine (eq_MA_inr _ _ _ _ _ @ _). simpl.
    match goal with
    | |- 1 = (?a1 @ (ap ?f (ap ?g ?h) @ (?a2  @ ?a3))) => refine (_ @ ap (fun T => a1 @ (T @ (a2 @ a3))) (ap_compose g f h))
    end.
    cbn.
    match goal with
    | |- 1 =  ?a1 @ (?a2 @  (ap ?f (ap ?g ?h) @ ?a3)) => refine (_ @ ap (fun T => a1 @ (a2 @ (T @ a3))) (ap_compose g f h))
    end.
    match goal with
    | |- 1 = ?q1 @ (?q2 @ (ap ?f ?p1^ @ ap ?g ?p2^)) => refine (_ @ ap (fun T => q1 @ (q2 @ (ap f p1^ @ T))) (concat_ap_V g p2)^);
                                                   refine (_ @ ap (fun T => q1 @ (q2 @ (T @ (ap g p2)^))) (concat_ap_V f p1)^)
    end.
    match goal with
    | |- 1 = (ap _ (FreeComposeMA ?G1 ?G2)) @ ?a1 =>  refine (_ @ ap (fun T => T  @ a1) (ap_FreecomposeMA_inr G1 G2 b)^)
    end. simpl.
    match goal with
    | |- 1 = (ap _ (FreeComposeMA ?F1 ?F2)) @ ?a1 =>  refine (_ @ ap (fun T => T @ a1) (ap_FreecomposeMA_inr F1 F2 (mkPair (ME G1 b,1) b,2 ))^)
    end. simpl.
    match goal with
    | |- 1 = (ap ?f (FreeComposeMA ?G1 ?G2)) ^ @ ?a1 =>
      change f with (compose (fun y => FreeMA G3 y) (fun x0 : [aug1 ]* -> [aug3 ]* => x0 (inr b)))
    end.
    unfold compose.
      match goal with
      |- 1 = (ap _ ?q)^ @ ?p => refine (_ @ ap (fun T => T^ @ p) (ap_compose (fun x0 => x0 (inr b)) (FreeMA G3) q)^)
    end.
    match goal with
    | |- 1 = (ap ?a2 (ap _ (FreeComposeMA ?G1 ?G2))) ^ @ ?a1 =>  refine (_ @ ap (fun T => (ap a2 T) ^ @ a1) (ap_FreecomposeMA_inr G1 G2 b)^)
    end. simpl.
    match goal with
    | |- 1 = (ap _ (FreeComposeMA ?G1 ?G2))^ =>  exact (ap (fun T => T^) (ap_FreecomposeMA_inr G1 G2 b)^)
    end.
  - intro a. refine (transport_lemma_dep _ _ _ _ _ _).
    match goal with
    | |- (ap (fun r => r @ ?p) (?q1 @ ?q2)) @ ?u1 = _ @ _ =>
      refine (ap (fun T => T @ u1) (ap_at _ _ _) @ _)
    end.
    rewrite 12!ap_at.
    match goal with
    | |- (ap (fun r => r @ ?p) ?q^ @ ?u) @ ?v = _ => refine (ap (fun T => (T @ u) @ v ) _ @ _)
    end.
    + match goal with
      | |- ap (fun r => r @ ?p) ?q^ = _ => refine (concat_ap_V (fun r => r @ p) q @ _)
      end.
      refine (ap (fun T => T^) _ @ _).
      match goal with
      | |- ap (fun r => r @ (ap ?t ?i)) ?q = _ =>  assert (i^^ = i)
      end.
      destruct (incoh a). reflexivity.

      FreeMA (ComposeMA (ComposeMA G1 G2) G3) (inl (d aug1 a)) =
      inl (compose ( compose f1 f2) f3) (d aug1 a)
      =
      inr (mkPair (compose (compose (ME G1) (ME G2)) (ME G3)  
       FreeMA (ComposeMA (ComposeMA G1 G2) G3)
         (inr {| fst := a,1; snd := Faces n a,2 |})
      
      destruct H.
    
    
    match goal with
    | |- (ap (fun r => r @ ?p) ?q11^) @ (ap (fun r => r @  _) (?q21 @ ?q22)) @ ?u1 = _ => idtac
                                                           end.
Admitted. 


               
  intro a. 
  unfold ComposeMA_assoc. unfold FreemposeMA.
 match goal with 

 | |- ap FreeMA (eq_MA ?a1 ?a2 ?a3 ?a4) = _ => simple refine ( (ap_FreeMA (F := F1) (F' := F4) a1 a2 a3 a4) @ _)
 end. 
 Admitted.
 
Lemma transport_compose {A A' : Type} (f : A -> A') (P : A' -> Type) {x y : A} (p : x = y) (u : P (f x)):
  transport (compose P f) p u = transport P (ap f p) u.
Proof.
  destruct p.
  reflexivity.
Defined.

Definition eq_MPol (n : nat) (P P' : Pol n) (aug : Aug (Free P) (S n)) (aug' : Aug (Free P') (S n))
           (f f' : MPol P P') (MF : MAug (FreeM f) aug aug') (MF' : MAug (FreeM f') aug aug')
           (p : f = f') (q : transport (fun W => MAug (FreeM W) aug aug') p  MF = MF') : ExtM f MF = ExtM f' MF'.
Proof.
  destruct p.
  destruct q.
  reflexivity.
Defined.



Lemma transport_transport (A B : Type) (f : A -> B) (P : B -> Type) (x y : A) (z : B) (p : x = y) (q : f x = z) (px : P z) :
  transport (fun W => P (f W)) p (transport P q^ px) = transport P (q^ @ ap f p) px.
Proof.
  destruct p. destruct q. reflexivity.
Defined.

Fixpoint ComposeM_assoc {n :nat} (p q r s : Pol n) (F : MPol p q) (G : MPol q r) (H : MPol r s) {struct n}:
  {c : ComposeM F (ComposeM G H) = ComposeM (ComposeM F G) H | ap FreeM c =
                                                               (FreeComposeM F (ComposeM G H))
                                                                 @ ap (fun W => compose W (FreeM F)) (FreeComposeM G H) 
                                                                 @ ap (fun W => compose (FreeM H) W) (FreeComposeM F G)^
                                                               @ (FreeComposeM (ComposeM F G) H)^}.
Proof.
  destruct n.
  - destruct p using case0. destruct q using case0. destruct r using case0. destruct s using case0.
    destruct F as [f] using (caseM0 _ _). destruct G as [g] using (caseM0 _ _). destruct H as [h] using (caseM0 _ _).
    simpl. unshelve econstructor.
    + reflexivity.
    + reflexivity.
  - destruct p as [p augp] using caseS'.  destruct q as [q augq] using caseS'.  destruct r as [r augr] using caseS'.  destruct s as [s augs] using caseS'.
    destruct F as [F Faug] using (caseMS' _ _ _ _ _).
    destruct G as [G Gaug] using (caseMS' _ _ _ _ _).
    destruct H as [H Haug] using (caseMS' _ _ _ _ _).
    simpl.
    unshelve econstructor.
    + simple refine (eq_MPol _ _ _ _ _ _ _ _ _ _ _).
      * exact (fstd (ComposeM_assoc n p q r s F G H)).
      * simpl. refine ((transport_transport _ _ _ _ _ _ _ _ _ _) @ _).
        rewrite (sndd (ComposeM_assoc n p q r s F G H)). simpl.

      
Admitted.

SearchAbout transport.

Lemma Forget_composeM (n : nat) ( T T' T'' : Type) (f : T -> T') (f' : T' -> T'') :
  ComposeM (ForgetM n f) (ForgetM n f') = ForgetM n (compose f' f).
Admitted.

Fixpoint ForgetTriangular (n : nat) (T : Type) {struct n} :
  ComposeM (Unit (Forget T n)) (ForgetM n (Counit T n)) = fstd IdAndFreeM (Forget T n).
Proof.
  destruct n.
  - exact 1.
  -  simpl. simple refine (eq_MPol _ _ _ _ _ _ _ _ _ _ _).
     + refine ((ComposeM_assoc _ _ _ _ _ _ _)^ @ _).
       unfold injectPol.
       refine ((ap (fun W => ComposeM (Unit (Forget T n)) W) (Forget_composeM _ _ _ _ _ _)) @ _).
       change (injectA (ForgetA (Counit T n) (S n))) with (injectPol _ (ForgetA (Counit T n) (S n))).
       refine ((ap (fun W => ComposeM (Unit (Forget T n)) (ForgetM n W)) (Counit_inject _ _ )) @ _).
       exact (ForgetTriangular n T).
    + simpl.