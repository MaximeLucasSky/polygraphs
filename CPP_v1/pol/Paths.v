(* This file contains some basic defintiions and some basic lemmas, 
in particular about equalities *)



Require Import Basics.

Set Primitive Projections.

Record Pair (A B : Type) :=
  mkPair {
      fst : A;
      snd : B
    }.


Notation "x .1" := (fst _ _ x) (at level 5).
Notation "x .2" := (snd _ _ x) (at level 5).
Arguments mkPair {_ _} _ _.

Notation "A × B " := (@Pair A B) (at level 20).

Notation "( a , b )" := (mkPair a b).


Record DPair {A : Type} (P : A -> Type): Type :=
  mkDPair
    {fstd : A;
     sndd : P (fstd)
    }.

Arguments fstd {_ _} _.
Arguments sndd {_ _} _.
Arguments mkDPair {_ _} _ _.

Notation "{ x : A | P }" := (DPair (A:=A) (fun x => P)) : type_scope.


Record  PullB {B1 B2 C : Type} (f1 : B1 -> C) (f2 : B2 -> C) : Type :=
  mkPullB
    {pi1 : B1;
     pi2 : B2;
     coh : f1 pi1 = f2 pi2
    }.

Arguments pi1 {_ _ _ _ _} _.
Arguments pi2 {_ _ _ _ _} _.
Arguments coh {_ _ _ _ _} _.
Arguments mkPullB {_ _ _ _ _} _ _ _.

Notation "1" := (eq_refl _).
Notation "p ^" := (eq_sym p) (at level 3) : type_scope.
Notation "p @ q" := (eq_trans p q) (at level 20) : type_scope.

SearchAbout eq_trans.


Definition concat_1p {A : Type} {x y: A}  (p : x = y) :  1 @ p = p :=
  match p with
  |1 => 1
  end.
Definition concat_pV {A : Type} {x y : A} (p : x = y) : p @ p^ = 1 :=
  match p with
  |1 => 1
  end.
Definition concat_Vp {A : Type} {x y : A} (p : x = y) : p^ @ p = 1 :=
  match p with
  |1 => 1
  end.
Definition concat_VV {A : Type} {x y : A} (p : x = y) : p^^ = p :=
  match p with
  |1 => 1
  end.
Definition concat_V {A : Type} {x y z : A} (p : x = y) (q : y = z) : (p @ q)^ = (q^ @ p ^).
Proof.
  destruct p. simpl.
  destruct q.
  exact 1.
Defined.

Definition assoc {A : Type} {x y z t: A} (p : x = y) (q : y = z) (r : z = t) : p @ (q @ r) = (p @ q) @ r.
Proof.
  destruct q, r. reflexivity.
Defined.

Notation "p # x" := (eq_rect _ _ x _ p) (right associativity, at level 65, only parsing): type_scope.

Definition f_equal_constant {A B : Type} (b : B) {x y : A} (p : x = y) : f_equal (fun _ => b) p = 1 :=
  match p with
  |1 => 1
  end.

Definition f_equal_id {A : Type} {x y : A} (p : x = y) : f_equal (fun x => x) p = p.
Proof.
  destruct p. exact 1.
Defined.


Lemma rewrite_f_equal {A B : Type} {f g : A -> B} (P : f = g) {x y : A} (p : x = y) :
  (f_equal (fun h => h x) (P ^)) @ f_equal f p @ (f_equal (fun h => h y) P) = f_equal g p.
Proof.
  destruct P, p. 
  reflexivity.
Defined.


Definition apd {A : Type} {B : A -> Type} (f : forall a:A, B a) {x y : A} (p : x = y):  p # f x = f y :=
  match p with
  |1 => 1
  end.

Arguments eq_rect {A x} P _ {y} _.

Lemma transport_lemma {T T' : Type}
      {x y : T} (p : x = y) (F : T -> T') (G : T -> T') (Hx : F x = G x) (Hy : F y = G y):
  Hx @ f_equal G p =  f_equal F p @ Hy ->  eq_rect (fun t => F t = G t) Hx p = Hy.
Proof.
  destruct p. simpl. intro H. rewrite concat_1p in H. exact H.
Defined.

Lemma transport_lambda {T T' : Type}
      {x y : T} (p : x = y) (F : T -> (T' -> Type)) (Hx : forall u : T', F x u) (a : T') :
  (eq_rect (fun (t : T) => forall  (u : T'), F t u) Hx p) a = eq_rect (fun (t : T) => F t a) (Hx a) p.
Proof.
  destruct p. reflexivity.
Defined.

Lemma image_transport  {A B: Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x)
      (f : forall a : A, P a -> B) :
  f _ (eq_rect P u p) = f _ u.
Proof.
  destruct p. reflexivity.
Defined.

Lemma ap_compose {T1 T2 T3: Type} (F: T1 -> T2) (G : T2 -> T3) {x y : T1} (p : x = y) :
  f_equal (fun x => G (F x)) p =  (f_equal G) _ _ ((f_equal F) _ _ p).
Proof.
  destruct p.
  reflexivity.
Defined.

Definition ap_concat {T1 T2 : Type} (F : T1 -> T2) {x y z : T1} (p : x = y) (q : y = z) : f_equal F (p @ q) = (f_equal F p) @ (f_equal F q).
Proof.
  destruct p. destruct q. reflexivity.
Defined.


Definition concat_ap_V {T1 T2 : Type} (F : T1 -> T2) {x y : T1} (p : x = y) : f_equal F (p ^) = (f_equal F p)^ := match p with
                                                                                                       |1 => 1
                                                                                                              end.


Lemma apap {A B : Type} (f : A -> B) {x y : A} {p q: x = y} (P : p = q) : f_equal f p = f_equal f q.
Proof.
  destruct P. reflexivity.
Defined.


Lemma eq_concat {A : Type} {x y y' z: A} (p : x = y) (p': x = y') (q : y = z) (q' : y' = z) (Hy : y = y') : p @ Hy = p' -> q = Hy @ q' -> p @ q = p' @ q'.
Proof.
  intros.
  exact ((f_equal (fun W => p @ W) H0) @ (assoc p Hy q') @ (f_equal (fun W => W @ q') H)).
Defined.
  
Lemma ap_ap_compose {T0 T1 T2 T3: Type} (F: T1 -> T2) (G : T2 -> T3) {x y : T0} (H : T0 -> T1) (p : x = y) :
  ap_compose F G (f_equal H p) = ((ap_compose H (compose G F) p)^ @ (ap_compose (compose F H) G p) @ f_equal (fun W => f_equal G W) (ap_compose H F p)).
Proof.
  destruct p. reflexivity.
Defined.


Lemma ap_along_id {A : Type} {x y : A} (p : x = y) : f_equal (fun x => x) p = p.
Proof.
  destruct p. exact 1.
Defined.


Definition square  {T T' : Type} {a b : T} {f g : T -> T'} (e : a = b) (p : f = g) : 
  f_equal (fun x => x a) p @ f_equal (fun x => g x) e = f_equal (fun x => f x) e @ f_equal (fun x => x b) p :> (f a = g b).
Proof.
  destruct e. simpl. exact ((concat_1p _)^).
Defined.


Lemma transport_lemma_dep
      {T T': Type} {a b : T} {f g : T -> T'} (e : a = b) (p q : f = g) (Ha : f_equal (fun x => x a) p = f_equal (fun x => x a) q)
      (Hb : f_equal (fun x => x b) p = f_equal (fun x => x b) q) :
  f_equal (fun r => r @ (f_equal (fun x => g x) e)) Ha @ (square e q) = (square e p) @ f_equal (fun r => (f_equal (fun x => f x) e) @ r) Hb
  -> eq_rect (fun x => (f_equal (fun h => h x) p = f_equal (fun h => h x) q)) Ha e = Hb :> (_ = _ :> (f b = g b)).
Proof.
  intro.
  destruct e.
  destruct p.
  simpl  in *.
  destruct Hb. simpl in H.
  refine ( _  @ H).
  now rewrite f_equal_id. 
Defined.

Lemma ap_at {T: Type} {x y z: T} {e1 e2 e3: x = y} (p : y = z) (q1: e1 = e2) (q2 : e2 = e3) :
  f_equal (fun r => r @ p) (q1 @ q2) = (f_equal (fun r => r @ p) q1) @ (f_equal (fun r => r @ p) q2).
Proof.
  destruct q1. simpl.
  rewrite (ap_concat _ _ _). simpl. reflexivity.
Defined.

Lemma VV {T : Type} {x y : T} (p : x = y) : p^^ = p.
  now destruct p.
Defined.

(** The next Lemmas deal with functional extensionality **)


Axiom FunExtDep_bad : forall {A : Type} {B : A -> Type} {f g : forall a : A, B a} (p : forall a : A, f a = g a),  @eq _ f  g.

Definition FunExtDep {A : Type} {B : A -> Type} {f g : forall x, B x} (p : forall x, f x = g x) : f = g.
Proof.
  exact ((FunExtDep_bad (fun x => 1))^ @ (FunExtDep_bad p)). 
Defined.

Lemma FunExtDep_refl {A : Type} {B : A -> Type} {f : forall x, B x} : FunExtDep (f := f) (fun x => 1) = 1.
Proof.
  exact (concat_Vp _).
Defined.

Lemma forall_eq_destruct {A : Type} {B : A -> Type} (f : forall a : A, B a) (P : { g : forall a : A, B a | forall a : A, f a = g a } -> Type)
      (H : P (mkDPair f (fun a => 1))) G : P G.
Proof.
  destruct G as [g p].
  set (g' := fun x => mkDPair (g x) (p x)). 
  change g with (fun x => fstd (g' x)).
  change p with (fun x => sndd (g' x)).
  clearbody g'; clear g p.
  cut (forall x, mkDPair (f x) 1 = g' x).
  - intro H'. apply FunExtDep in H'. destruct H'.
    simpl. exact H.
  -  intro x. destruct (g' x) as [gx p].
     destruct p. reflexivity.
Defined.

Lemma f_understood {A : Type} (x : A) (F : forall a : A, x = a -> x = a) : forall a : A, forall p : x = a, F a p = F x 1 @ p.  
Proof.
  now destruct p.
Defined.

Lemma f_understood_forall {A : Type} {P : A -> Type} (f : forall a : A, P a)
      (F : forall g : (forall a : A, P a),   (forall a : A, f a = g a) -> (forall a : A, f a = g  a)) :
  forall a : A, forall g : forall a : A, P a, forall p : forall a : A, f a = g a,
        F g p a = F f (fun a => 1) a @ (p a).
Proof.
  intros.
  set (q := fun a => mkDPair (g a) (p a)). 
  change g with (fun a => fstd (q a)). change p with (fun a => (sndd (q a))). clearbody q. clear g p.
  cut ((fun a => mkDPair (f a) 1) = q).
  - intro. simpl. destruct H.  simpl. reflexivity.
  - apply FunExtDep. intro x'. destruct (q x'). destruct sndd0. reflexivity.
Defined.

Lemma ap_FunExt {A : Type} {P : A -> Type} {f g : forall a : A, P a}  (p : forall a : A, f a = g a) (x : A):
  f_equal (fun W => W x) (FunExtDep p) = p x.
Proof.
  Check (fun (g : forall a : A, P a) (p : forall a : A, f a = g a) => (fun a => f_equal (fun W => W a) (FunExtDep p))).
  simple refine (f_understood_forall f (fun g (p : forall a : A, f a = g a) => (fun a => f_equal (fun W => W a) (FunExtDep p))) x g p @ _). simpl.
  match goal with
  | |- f_equal ?f _ @ p x = p x => 
    exact ((f_equal (fun W => (f_equal f W @ p x)) FunExtDep_refl) @ concat_1p _)
  end. 
Defined.

Lemma FunExt_ap {A : Type} {P : A -> Type} {f g : forall a : A, P a}  (p : f = g) :
  FunExtDep (fun x => f_equal (fun W => W x) p) = p.
Proof.
  simple refine (f_understood f (fun g (p : f = g) => FunExtDep (fun x => f_equal (fun W => W x) p)) g p @ _). simpl.
  exact (f_equal (fun W => W @ p) (FunExtDep_refl) @ concat_1p _).
Defined.
  

Definition funext {X Y : Type} {f g : X -> Y} (p : forall x : X, f x = g x) : f = g := FunExtDep p. 

Definition funextcompute {X Y : Type} {f g : X -> Y} (p : forall x : X, f x = g x) (x : X) : f_equal (fun H => H x) (funext p) = p x :=
  ap_FunExt p x. 

Opaque FunExtDep.

Lemma FunExtDep_injective  {A : Type} {B : A -> Type} {f g : forall a : A, B a} (p q : forall a : A, f a = g a) :
  FunExtDep p = FunExtDep q -> p = q.
Proof.
  intro.
  apply FunExtDep.
  intro x. simple refine ((ap_FunExt p x)^ @ _ @ (ap_FunExt q x)).
  exact (f_equal _ H).
Defined.
  

Lemma eq_fun {A : Type} {B : A -> Type} {f g : forall a : A, B a} (p q : f = g) : (forall a : A, f_equal (fun h => h a) p = f_equal (fun h => h a) q) -> p = q.
Proof.
  intro.
  simple refine ((FunExt_ap p)^ @ _ @ (FunExt_ap q)).
  exact (f_equal FunExtDep (FunExtDep H)).
Defined.



Lemma destruct_fun_eq {E X} {A : E -> X -> Type}
      (P : forall G1 G2 q, Type) (H : forall G, P G G (fun e x => 1))
  {G1 : forall e x, A e x} {G2 : forall e x, A e x} (q : forall e x, G1 e x = G2 e x): P G1 G2 q.
Proof.
  set (q' := FunExtDep (fun e => (FunExtDep (fun x => q e x)))).
  assert ((fun e x => (f_equal (fun W => W e x) q')) = q).
  { subst q'. repeat (apply FunExtDep; intro).
    rewrite (ap_compose (fun W => W x) (fun W => W x0)).
    rewrite (ap_FunExt (fun e => FunExtDep (fun x1 : X => q e x1)) x).
    rewrite ap_FunExt. reflexivity.
  }
  clearbody q'. destruct H0. destruct q'. apply H.
Defined.


Lemma forall_eq_rect {A : Type} {B : A -> Type} (f : forall a : A, B a) (P : forall g : (forall a : A, B a),  ((forall a : A, f a = g a)  -> Type))
      (H : P f (fun a => 1)) g p : P g p.
Proof.
  exact (forall_eq_destruct f (fun G => P (fstd G) (sndd G)) H (mkDPair g p)).
Defined.

