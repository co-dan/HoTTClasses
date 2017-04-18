Require Import
  HoTT.Types.Arrow
  HoTT.Types.Universe
  HoTT.Basics
  HoTT.HIT.Truncations.
Require Import
  HoTTClasses.interfaces.abstract_algebra.

Lemma injective_compose_cancel `{Funext} {A B C : Type} (f : B → C)
    `{!Injective f} {g : A → B} {h : A → B} :
  f ∘ g = f ∘ h → g = h.
Proof.
  intros E. apply path_arrow;intros x.
  apply (injective f).
  apply (ap (fun F => F x) E).
Qed.

Lemma surjective_applied {A B : Type} (f : A → B) `{!Inverse f} `{!Surjective f} x
 : f (f⁻¹ x) = x.
Proof.
change ((f ∘ (f ⁻¹)) x = id x).
apply (ap (fun F => F x)).
apply (surjective f).
Qed.

Lemma bijective_cancel_left {A B : Type} (f : A → B) `{!Inverse f}
  `{!Bijective f} x y
 : f x = y → x = f⁻¹ y.
Proof.
  intros E.
  apply (injective f).
  rewrite (surjective_applied f).
  assumption.
Qed.

Lemma bijective_cancel_inverse_left {A B : Type} (f : A → B)
  `{!Inverse f} `{!Bijective f} x y
  : f⁻¹ x = y → x = f y.
Proof.
  intros E.
  rewrite <-E, (surjective_applied f).
  reflexivity.
Qed.

Lemma bijective_applied `(f : A → B) `{!Inverse f} `{!Bijective f} x: f⁻¹ (f x) = x.
Proof.
  symmetry. apply (bijective_cancel_left f). reflexivity.
Qed.

Lemma bijective `{Funext} `(f : A → B) `{!Inverse f} `{!Bijective f} : f⁻¹ ∘ f = id.
(* a.k.a. "split-mono" *)
Proof.
  apply path_forall. intros x.
  apply (bijective_applied f).
Qed.

Lemma injective_ne `(f : A → B) `{!Injective f} x y :
  x ≠ y → f x ≠ f y.
Proof.
intros E1 E2. apply E1.
apply (injective f).
assumption.
Qed.

Instance id_inverse {A} : Inverse (@id A) := (@id A).

Instance id_injective {A : Type} : Injective (@id A).
Proof. red;trivial. Qed.
Instance id_surjective {A : Type} : Surjective (@id A).
Proof. red;trivial. Qed.
Instance id_bijective {A : Type} : Bijective (@id A).
Proof. split; try apply _. Qed.

Section compositions.
  Context {A B C : Type} (g: A → B) (f: B → C) `{!Inverse f} `{!Inverse g}.

  Instance compose_inverse: Inverse (f ∘ g) := g⁻¹ ∘ f⁻¹.

  Instance compose_injective: Injective f → Injective g → Injective (f ∘ g).
  Proof.
  red;intros.
  apply (injective g).
  apply (injective f).
  assumption.
  Qed.

  Instance compose_surjective : Surjective f → Surjective g →
    Surjective (f ∘ g).
  Proof.
  red;intros.
  change (compose f (compose (compose g (inverse g)) (inverse f)) = id).
  rewrite (surjective g).
  apply (surjective f).
  Qed.

  Instance compose_bijective : Bijective f → Bijective g → Bijective (f ∘ g)
    := {}.
End compositions.

Hint Extern 4 (Inverse (_ ∘ _)) =>
  class_apply @compose_inverse : typeclass_instances.
Hint Extern 4 (Injective (_ ∘ _)) =>
  class_apply @compose_injective : typeclass_instances.
Hint Extern 4 (Surjective (_ ∘ _)) =>
  class_apply @compose_surjective : typeclass_instances.
Hint Extern 4 (Bijective (_ ∘ _)) =>
  class_apply @compose_bijective : typeclass_instances.

Lemma alt_Build_Injective `(f : A → B) `{!Inverse f} : f⁻¹ ∘ f = id → Injective f.
Proof.
intros E x y F.
path_via (id x).
rewrite <- (ap (fun F => F x) E).
path_via (id y); rewrite <- (ap (fun F => F y) E).
unfold compose. rewrite F. reflexivity.
Qed.

Lemma alt_Build_Bijective `(f : A → B) `{!Inverse f} :
  f⁻¹ ∘ f = id → f ∘ f⁻¹ = id → Bijective f.
Proof.
intros. split.
- apply (alt_Build_Injective f). assumption.
- red; assumption.
Qed.

Definition inverse_inverse `{Inverse A B f} : Inverse (f⁻¹) := f.
Hint Extern 4 (Inverse (_ ⁻¹)) =>
  class_apply @inverse_inverse : typeclass_instances.

Lemma flip_bijection `{Funext} `{Bijective A B f} : Bijective (f⁻¹).
Proof.
apply alt_Build_Bijective.
- apply (surjective f).
- apply path_forall. intros x.
  apply (bijective_applied f).
Qed.

(* We use this instead of making flip_bijection a real instance, because
   otherwise it gets applied too eagerly, resulting in cycles. *)
Hint Extern 4 (Bijective (_ ⁻¹)) => apply flip_bijection : typeclass_instances.

Lemma inverse_involutive `(f : A → B) `{!Inverse f} : (f⁻¹)⁻¹ = f.
Proof. reflexivity. Qed.

(* This second version is strictly for manual application. *)
Lemma flip_bijection_back `{Funext} `(f: A → B) `{!Inverse f}
 : Bijective (f⁻¹) → Bijective f.
Proof. intro. apply (_: Bijective (f⁻¹⁻¹)). Qed.

Ltac setoid_inject :=
  match goal with
  | E : _ = ?f _ |- _ => apply (injective f) in E
  | E : ?f _ = _ |- _ => apply (injective f) in E
  | E : _ = _ |-  ?G => change (id G); injection E; clear E; intros;
    unfold id at 1 
  end.


Section surjective_factor.
Context `{Funext}.
Context `{IsHSet C} `(f : A -> C) `(g : A -> B) {Esurj : IsSurjection g}.
Variable (Eg : forall x y, g x = g y -> f x = f y).

Definition is_img (x : B) (y : C) := merely (exists z : A, x = g z /\ y = f z).

Definition surjective_factor_auxT x := sigT (fun y => is_img x y).

Instance surjective_factor_aux_ishprop
  : forall x, IsHProp (surjective_factor_auxT x).
Proof.
intros. apply Sigma.ishprop_sigma_disjoint.
unfold is_img;intros y1 y2 E1;apply (Trunc_ind _);intros [z2 [E3 E4]].
revert E1;apply (Trunc_ind _);intros [z1 [E1 E2]].
path_via (f z1);path_via (f z2).
apply Eg. path_via x.
Qed.

Definition surjective_factor_aux : forall x, surjective_factor_auxT x.
Proof.
intros x. generalize (center _ (Esurj x)). apply (Trunc_ind _).
intros z. exists (f z.1).
apply tr. exists z.1;split;trivial. symmetry;trivial.
Defined.

Definition surjective_factor : B -> C :=
  fun x => (surjective_factor_aux x).1.

Lemma surjective_factor_pr : f = compose surjective_factor g.
Proof.
apply path_forall. intros x.
unfold surjective_factor,surjective_factor_aux,compose. simpl.
set (Y := (center
           (TrM.Os_ReflectiveSubuniverses.O_reflector
              (modality_to_reflective_subuniverse (trunc_S minus_two))
              (hfiber g (g x))))).
generalize Y. clear Y.
apply (Trunc_ind _).
intros Y. simpl.
apply Eg. symmetry;apply Y.2.
Qed.

End surjective_factor.



Class IsApEquiv {A B} (f:A -> B) := isapequiv :> forall x y, IsEquiv (@ap _ _ f x y).

Lemma embedding_apequiv {A B} (f : A -> B) : IsEmbedding f -> IsApEquiv f.
Proof.
  intros E x y.
  simple refine (isequiv_adjointify _ _ _ _).
  - intros e. red in E.
    pose proof (path_ishprop ((x;e): hfiber f (f y)) ((y;idpath): hfiber f (f y))) as e'.
    exact (ap pr1 e').
  - intros e.
    simpl. set (e' := path_ishprop _ _).
    pose (e1 := (Sigma.equiv_path_sigma _ _ _)^-1 e').
    simpl in e1. change (ap f e1.1 = e). clearbody e1. destruct e1 as [e1 e2].
    destruct e1. simpl in *. exact e2^.
  - intros e;destruct e;simpl.
    set (e' := path_ishprop _ _).
    exact (transport (fun e' => ap pr1 e' = idpath) (path_ishprop idpath e') idpath).
Defined.

Lemma apequiv_embedding {A B} (f : A -> B) : IsApEquiv f -> IsEmbedding f.
Proof.
  intros E y. apply hprop_allpath.
  intros [x px] [x' px']. destruct px'.
  revert px. apply (equiv_ind (ap f)).
  intros e. destruct e. reflexivity.
Defined.

Definition truncmap_isequiv {A B} (f : A -> B) : IsTruncMap (-2) f -> IsEquiv f
  := EquivalenceVarieties.isequiv_fcontr _.

Definition isequiv_truncmap {A B} (f:A -> B) : IsEquiv f -> IsTruncMap (-2) f
  := EquivalenceVarieties.fcontr_isequiv _.

Definition truncmap_S_ap_truncmap {A B} n (f:A -> B)
  : IsTruncMap (trunc_S n) f ->
    forall x y, IsTruncMap n (@ap _ _ f x y)
  := fun E x x' y =>
       trunc_equiv' _ (Fibrations.hfiber_ap y)^-1.

Lemma ap_truncmap_truncmap_S {A B} n (f:A -> B)
  : (forall x y, IsTruncMap n (@ap _ _ f x y)) ->
    IsTruncMap (trunc_S n) f.
Proof.
  intros E y a b;
    change (IsTrunc n (a = b)).
  destruct a as [a p], b as [b q].
  destruct q.
  exact (trunc_equiv' _ (Fibrations.hfiber_ap p)).
Defined.

Instance embedding_apequiv_alt {A B} (f : A -> B) : IsEmbedding f -> IsApEquiv f.
Proof.
  intros E x y. apply EquivalenceVarieties.isequiv_fcontr,truncmap_S_ap_truncmap,E.
Qed.

Lemma apequiv_embedding_alt {A B} (f : A -> B) : IsApEquiv f -> IsEmbedding f.
Proof.
  intros E. apply ap_truncmap_truncmap_S. intros x y;red;apply EquivalenceVarieties.fcontr_isequiv,E.
Qed.

Instance apequiv_compose {A B C} (f:A->B) (g:B->C) `{!IsApEquiv f} `{!IsApEquiv g}
  : IsApEquiv (compose g f).
Proof.
  intros x y.
  apply (isequiv_homotopic (compose (@ap _ _ g (f x) (f y)) (@ap _ _ f x y))).
  intros p. symmetry;apply (ap_compose f g).
Defined.

Instance equiv_apequiv {A B} (f : A -> B) `{!IsEquiv f} : IsApEquiv f := isequiv_ap.

(** Example showing IsApEquiv S. *)
Definition nat_encode_step x y
  := match x, y with
     | O, O => Unit
     | S x, S y => x = y
     | _, _ => Empty
     end.

Lemma nat_encode_step_refl : forall x, nat_encode_step x x.
Proof.
  intros [|x];simpl;trivial.
Defined.

Definition nat_encode_step_to : forall x y, x = y -> nat_encode_step x y
  := fun x y e => transport _ e (nat_encode_step_refl x).

Lemma nat_encode_step_from : forall x y, nat_encode_step x y -> x = y.
Proof.
  intros x y;destruct x as [|x], y as [|y];simpl;intros e;
    solve [destruct e|trivial|apply (ap S e)].
Defined.

Definition nat_encode_step_equiv_to : forall x y, IsEquiv (nat_encode_step_to x y).
Proof.
  intros x y;simple refine (BuildIsEquiv _ _ _ (nat_encode_step_from x y) _ _ _).
  - destruct x as [|x], y as [|y];try solve [exact (Empty_ind _)];intros e;simpl in *.
    + apply Unit.eta_unit.
    + destruct e;reflexivity.
  - intros e;destruct e, x as [|x];simpl;reflexivity.
  - intros e;destruct e, x as [|x];simpl;reflexivity.
Defined.

Definition nat_encode_step_equiv_from : forall x y, IsEquiv (nat_encode_step_from x y)
  := fun x y => @isequiv_inverse _ _ _ (nat_encode_step_equiv_to x y).

Instance S_apequiv : IsApEquiv S.
Proof.
  intros x y.
  exact (nat_encode_step_equiv_from (S x) (S y)).
Defined.

Section BinTree.
  (* Example inductive with multiple recursive arguments *)
  Variable A : Type.
  Inductive BinTree :=
  | Leaf : A -> BinTree
  | Node : BinTree -> BinTree -> BinTree.

  Definition Node' xy := Node (fst xy) (snd xy).

  Definition bintree_encode_step x y
    := match x, y with
       | Leaf x, Leaf y => x = y
       | Node x1 x2, Node y1 y2 => (x1,x2) = (y1,y2)
       | _, _ => Empty
       end.

  Definition bintree_encode_step_refl x : bintree_encode_step x x.
  Proof. destruct x as [x|x1 x2];simpl;auto. Defined.

  Definition bintree_encode_step_to x y : x = y -> bintree_encode_step x y
    := fun e => transport _ e (bintree_encode_step_refl x).

  Definition bintree_encode_step_from x y : bintree_encode_step x y -> x = y.
  Proof.
    destruct x as [x|x1 x2], y as [y|y1 y2];simpl;try exact (Empty_rec _).
    - apply ap.
    - intros p. change (Node' (x1,x2) = Node' (y1,y2)). apply ap. trivial.
  Defined.

  Definition bintree_encode_step_equiv_to : forall x y, IsEquiv (bintree_encode_step_to x y).
  Proof.
    intros x y;simple refine (BuildIsEquiv _ _ _ (bintree_encode_step_from x y) _ _ _).
    - destruct x as [x|x1 x2], y as [y|y1 y2];try solve [exact (Empty_ind _)];simpl in *.
      + intros e;destruct e;reflexivity.
      + red. apply (equiv_ind (Prod.equiv_path_prod _ _));simpl.
        intros [[] []];reflexivity.
    - intros e;destruct e, x as [x|x1 x2];simpl;reflexivity.
    - intros e;destruct e, x as [x|x1 x2];simpl;reflexivity.
  Defined.

  Definition bintree_encode_step_equiv_from : forall x y, IsEquiv (bintree_encode_step_from x y)
    := fun x y => @isequiv_inverse _ _ _ (bintree_encode_step_equiv_to x y).

  Instance Node_apequiv : IsApEquiv Node'.
  Proof.
    intros xy xy'.
    pose proof (bintree_encode_step_equiv_from (Node' xy) (Node' xy')) as e.
    simpl in e. destruct xy as [x y], xy' as [x' y']. exact e.
  Defined.

End BinTree.
