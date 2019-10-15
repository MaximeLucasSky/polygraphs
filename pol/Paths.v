Set Primitive Projections.



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

(* Inductive  paths (A : Type) : A -> A -> Type := *)
(*   idpath (a : A) : paths A a a. *)


(* Notation "x = y :> A" := (paths A x y) : type_scope. *)
(* Notation "x = y" := (x = y :>_) : type_scope. *)

(* Arguments idpath {A a}, [A] a. *)

Notation "1" := (eq_refl _). 



Definition proj0 {A : Type} {x y : A} (p : x = y) : A := x.
Definition proj1 {A : Type} {x y : A} (p : x = y) : A := y.

Notation "p .0" := (proj0 p) (at level 3) : type_scope.
Notation "p .1" := (proj1 p) (at level 3) : type_scope.


Definition inverse {A : Type} {x y : A} (p : x = y) : (y = x) :=
  match p with
  |eq_refl _ => eq_refl _
  end.

Arguments inverse {A x y} p : simpl nomatch.

Notation "p ^" := (inverse p) (at level 3) : type_scope.


Definition concat {A: Type} {x y z : A} (p : x = y) (q : y = z) : (x = z).
  destruct p. exact q.
Defined.

Arguments concat {A x y z} p q : simpl nomatch.

Notation "p @ q" := (concat p q) (at level 20) : type_scope.


Definition concat_p1 {A : Type} {x y: A}  (p : x = y) :  p @ 1 = p :=
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
  destruct p, q. reflexivity.
Defined.

Definition compose {A B C : Type} (f : B -> C) (g : A -> B) : A -> C := fun (x : _) => f (g x).

Lemma compose_assoc {A B C D : Type} (f : C -> D) (g : B -> C) (h : A -> B) : compose f (compose g h) = compose ( compose f g) h.
Proof.
  constructor.
Defined.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p: x = y) (u : P x): P y.
  destruct p. exact u.
Defined.

Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing): type_scope.


Definition ap {A B : Type} (f: A -> B) {x y : A} (p : x = y): f x = f y :=
  match p with
  |1 => 1
  end.
Arguments ap {A B} f {x y} p : simpl nomatch.

Definition ap_constant {A B : Type} (b : B) {x y : A} (p : x = y) : ap (fun _ => b) p = 1 :=
  match p with
  |1 => 1
  end.

Definition ap_id {A : Type} {x y : A} (p : x = y) : ap (fun x => x) p = p.
Proof.
  destruct p. exact 1.
Defined.


Lemma rewrite_ap {A B : Type} {f g : A -> B} (P : f = g) {x y : A} (p : x = y) : (ap (fun h => h x) (P ^)) @ ap f p @ (ap (fun h => h y) P) = ap g p.
Proof.
  destruct P, p. 
  constructor.
Defined.

Definition apd {A : Type} {B : A -> Type} (f : forall a:A, B a) {x y : A} (p : x = y):  p # f x = f y :=
  match p with
  |1 => 1
  end.


 
Lemma transport_lemma {T T' : Type}
      {x y : T} (p : x = y) (F : T -> T') (G : T -> T') (Hx : F x = G x) (Hy : F y = G y):
  Hx @ ap G p =  ap F p @ Hy -> transport (fun t => F t = G t) p Hx = Hy.
Proof.
  destruct p. simpl. intro H. rewrite concat_p1 in H. exact H.
Defined.

Lemma transport_lambda {T T' : Type}
      {x y : T} (p : x = y) (F : T -> (T' -> Type)) (Hx : forall u : T', F x u) (a : T') :
  (transport (fun (t : T) => forall  (u : T'), F t u) p Hx) a = transport (fun (t : T) => F t a) p (Hx a).
Proof.
  destruct p. reflexivity.
Defined.

Lemma image_transport  {A B: Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) (f : forall a : A, P a -> B) :
  f _ (transport P p u) = f _ u.
Proof.
  destruct p. reflexivity.
Defined.

Lemma ap_compose {T1 T2 T3: Type} (F: T1 -> T2) (G : T2 -> T3) {x y : T1} (p : x = y) : ap (fun x => G (F x)) p =  (ap G) ((ap F) p).
Proof.
  destruct p.
  reflexivity.
Defined.

Definition ap_concat {T1 T2 : Type} (F : T1 -> T2) {x y z : T1} (p : x = y) (q : y = z) : ap F (p @ q) = (ap F p) @ (ap F q).
Proof.
  destruct p. destruct q. reflexivity.
Defined.

Print ap_compose.

Definition concat_ap_V {T1 T2 : Type} (F : T1 -> T2) {x y : T1} (p : x = y) : ap F (p ^) = (ap F p)^ := match p with
                                                                                                       |1 => 1
                                                                                                              end.



Definition footransportrew {A : Type} (P : A -> Type) {x y : A} (p: y = x) (u : P x) : P y.
Proof.
  rewrite p.
  exact u.
Defined.



(* Lemma transport_rew {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P y) : *)
(*   (p ^) # u = internal_paths_rew_r A x y P u p. *)
(* Proof. *)
(*   destruct p. reflexivity. *)
(* Defined. *)


(* Lemma rew_through_pair (A : Type) (a y : A) (T : Type) (Q : A -> T -> Type) (b : {g : T & Q y g}) (p : a = y) : *)
(*   internal_paths_rew_r A a y (fun a : A => {g : T & Q a g}) b p = *)
(*   existT _ (projT1 b) (internal_paths_rew_r A a y (fun a : A => Q a (projT1 b)) (projT2 b) p). *)
(* Proof. *)
(*   destruct p. destruct b. *)
(*   reflexivity. *)
(* Defined. *)


(* Lemma compute_rewrite {T U : Type} {t u : T} (f : T -> U) (p : t = u): *)
(*   internal_paths_rew T t (fun x : T => (f t = f x)) 1 u p = ap f p. *)
(* Proof. *)
(*   destruct p. reflexivity. *)
(* Defined. *)


(* Lemma compute_rewrite_r {T U : Type} {t u : T} (f : T -> U) (p : u = t): *)
(*   internal_paths_rew_r T u t (fun x : T => (f t = f x)) 1 p = ap f p^. *)
(* Proof. *)
(*   destruct p. reflexivity. *)
(* Defined. *)


Definition FunExtDep_bad {A : Type} {B : A -> Type} {f g : forall a : A, B a} (p : forall a : A, f a = g a) : @eq _ f  g.
Admitted.



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
  destruct p.
  exact ((concat_p1 _)^).
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
  - intro. simpl. destruct H.  simpl.  exact ((concat_p1 _)^).
  - apply FunExtDep. intro x'. destruct (q x'). destruct sndd0. reflexivity.
Defined.

Lemma ap_FunExt {A : Type} {P : A -> Type} {f g : forall a : A, P a}  (p : forall a : A, f a = g a) (x : A):
  ap (fun W => W x) (FunExtDep p) = p x.
Proof.
  Check (fun (g : forall a : A, P a) (p : forall a : A, f a = g a) => (fun a => ap (fun W => W a) (FunExtDep p))).
  simple refine (f_understood_forall f (fun g (p : forall a : A, f a = g a) => (fun a => ap (fun W => W a) (FunExtDep p))) x g p @ _). simpl.
  match goal with
  | |- ap ?f _ @ p x = p x => 
    exact (ap (fun W => (ap f W @ p x)) FunExtDep_refl)
  end. 
Defined.

Lemma FunExt_ap {A : Type} {P : A -> Type} {f g : forall a : A, P a}  (p : f = g) :
  FunExtDep (fun x => ap (fun W => W x) p) = p.
Proof.
  simple refine (f_understood f (fun g (p : f = g) => FunExtDep (fun x => ap (fun W => W x) p)) g p @ _). simpl.
  exact (ap (fun W => W @ p) (FunExtDep_refl)).
Defined.
  

Definition funext {X Y : Type} {f g : X -> Y} (p : forall x : X, f x = g x) : f = g := FunExtDep p. 

Definition funextcompute {X Y : Type} {f g : X -> Y} (p : forall x : X, f x = g x) (x : X) : ap (fun H => H x) (funext p) = p x :=
  ap_FunExt p x. 

Opaque FunExtDep.

Lemma FunExtDep_injective  {A : Type} {B : A -> Type} {f g : forall a : A, B a} (p q : forall a : A, f a = g a) :
  FunExtDep p = FunExtDep q -> p = q.
Proof.
  intro.
  apply FunExtDep.
  intro x. simple refine ((ap_FunExt p x)^ @ _ @ (ap_FunExt q x)).
  exact (ap _ H).
Defined.
  

Lemma eq_fun {A : Type} {B : A -> Type} {f g : forall a : A, B a} (p q : f = g) : (forall a : A, ap (fun h => h a) p = ap (fun h => h a) q) -> p = q.
Proof.
  intro.
  simple refine ((FunExt_ap p)^ @ _ @ (FunExt_ap q)).
  exact (ap FunExtDep (FunExtDep H)).
Defined.
  