/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import morphisms.ring_hom_properties
import ring_theory.ring_hom.finite_type

/-!
# Morphisms of finite type

A morphism of schemes `f : X ⟶ Y` is locally of finite type if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite type.

A morphism of schemes is of finite type if it is both locally of finite type and quasi-compact.

We show that these properties are local, and are stable under compositions.

-/

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universes v u

namespace algebraic_geometry

variables {X Y : Scheme.{u}} (f : X ⟶ Y)

/--
A morphism of schemes `f : X ⟶ Y` is locally of finite type if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite type.
-/
@[mk_iff]
class locally_of_finite_type (f : X ⟶ Y) : Prop :=
(finite_type_of_affine_subset :
  ∀ (U : Y.affine_opens) (V : X.affine_opens) (e : V.1 ≤ (opens.map f.1.base).obj U.1),
  (f.app_le e).finite_type)

lemma locally_of_finite_type_eq :
  @locally_of_finite_type = affine_locally @ring_hom.finite_type :=
begin
  ext X Y f,
  rw [locally_of_finite_type_iff, affine_locally_iff_affine_opens_le],
  exact ring_hom.finite_type_respects_iso
end

@[priority 900]
instance locally_of_finite_type_of_is_open_immersion {X Y : Scheme} (f : X ⟶ Y)
  [is_open_immersion f] : locally_of_finite_type f :=
locally_of_finite_type_eq.symm ▸
  ring_hom.finite_type_is_local.affine_locally_of_is_open_immersion f

lemma locally_of_finite_type_stable_under_composition :
  morphism_property.stable_under_composition @locally_of_finite_type :=
locally_of_finite_type_eq.symm ▸
ring_hom.finite_type_is_local.affine_locally_stable_under_composition

instance locally_of_finite_type_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [hf : locally_of_finite_type f] [hg : locally_of_finite_type g] :
  locally_of_finite_type (f ≫ g) :=
locally_of_finite_type_stable_under_composition f g hf hg

lemma locally_of_finite_type_of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [hf : locally_of_finite_type (f ≫ g)] :
  locally_of_finite_type f :=
begin
  unfreezingI { revert hf },
  rw [locally_of_finite_type_eq],
  apply ring_hom.finite_type_is_local.affine_locally_of_comp,
  introv H,
  exactI ring_hom.finite_type.of_comp_finite_type H,
end

lemma locally_of_finite_type.affine_open_cover_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
  (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)]
  (𝒰' : ∀ i, Scheme.open_cover.{u} ((𝒰.pullback_cover f).obj i))
  [∀ i j, is_affine ((𝒰' i).obj j)] :
  locally_of_finite_type f ↔
    (∀ i j, (Scheme.Γ.map ((𝒰' i).map j ≫ pullback.snd).op).finite_type) :=
locally_of_finite_type_eq.symm ▸ ring_hom.finite_type_is_local.affine_open_cover_iff f 𝒰 𝒰'

lemma locally_of_finite_type.source_open_cover_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
  (𝒰 : Scheme.open_cover.{u} X) :
  locally_of_finite_type f ↔ (∀ i, locally_of_finite_type (𝒰.map i ≫ f)) :=
locally_of_finite_type_eq.symm ▸ ring_hom.finite_type_is_local.source_open_cover_iff f 𝒰

lemma locally_of_finite_type.open_cover_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
  (𝒰 : Scheme.open_cover.{u} Y) :
  locally_of_finite_type f ↔
    (∀ i, locally_of_finite_type (pullback.snd : pullback f (𝒰.map i) ⟶ _)) :=
locally_of_finite_type_eq.symm ▸
  ring_hom.finite_type_is_local.is_local_affine_locally.open_cover_iff f 𝒰

lemma locally_of_finite_type_respects_iso :
  morphism_property.respects_iso @locally_of_finite_type :=
locally_of_finite_type_eq.symm ▸ target_affine_locally_respects_iso
  (source_affine_locally_respects_iso ring_hom.finite_type_respects_iso)

lemma locally_of_finite_type_is_local_at_target :
  property_is_local_at_target @locally_of_finite_type :=
locally_of_finite_type_eq.symm ▸
  (source_affine_locally_is_local ring_hom.finite_type_respects_iso
    ring_hom.finite_type_is_local.localization_preserves 
     ring_hom.finite_type_is_local.of_localization_span).target_affine_locally_is_local

-- move me
lemma subalgebra.map_top {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]
  [algebra R S] [algebra R T] (f : S →ₐ[R] T) : (⊤ : subalgebra R S).map f = f.range := 
begin
  ext, simp,
end

-- move me
lemma _root_.ring_hom.finite_type_stable_under_base_change :
  ring_hom.stable_under_base_change @ring_hom.finite_type :=
begin
  classical,
  rintros R S T _ _ _ _ i7 ⟨⟨s, hs⟩⟩,
  resetI,
  suffices : algebra.finite_type S (tensor_product R S T),
  { delta ring_hom.finite_type, convert this, apply algebra.algebra_ext, intro _, refl },
  replace hs : algebra.adjoin R (↑s : set T) = ⊤,
  { have : i7 = (algebra_map R T).to_algebra := algebra.algebra_ext _ _ (λ _, rfl), convert hs },
  refine ⟨⟨s.image algebra.tensor_product.include_right, _⟩⟩,
  rw [finset.coe_image, ← @algebra.adjoin_adjoin_of_tower R S (tensor_product R S T),
    algebra.adjoin_image, hs, subalgebra.map_top, eq_top_iff],
  rintro x -,
  induction x using tensor_product.induction_on with x y x y hx hy,
  { exact zero_mem _ },
  { convert_to x • ((1 : S) ⊗ₜ y) ∈ _,
    { rw [tensor_product.smul_tmul', ← algebra.algebra_map_eq_smul_one], refl },
    { exact subalgebra.smul_mem _ (algebra.subset_adjoin ⟨y, rfl⟩) _ } },
  { exact add_mem hx hy }
end

lemma locally_of_finite_type_stable_under_base_change :
  morphism_property.stable_under_base_change @locally_of_finite_type :=
locally_of_finite_type_eq.symm ▸
  ring_hom.finite_type_is_local.affine_locally_stable_under_base_change
    ring_hom.finite_type_stable_under_base_change

-- generalize me
lemma locally_of_finite_type_Spec_iff {R S : CommRing} (f : R ⟶ S) :
  locally_of_finite_type (Scheme.Spec.map f.op) ↔ ring_hom.finite_type f :=
begin
  transitivity (@affine ⊓ @locally_of_finite_type) (Scheme.Spec.map f.op),
  { refine (and_iff_right _).symm, apply_instance },
  { rw [locally_of_finite_type_eq, ← ring_hom.property_is_local.affine_and_eq,
      (is_local_affine_and _ _ _ _).affine_target_iff, affine_and_Spec_iff],
    exacts [ring_hom.finite_type_respects_iso, ring_hom.finite_type_respects_iso,
      ring_hom.finite_type_is_local.localization_preserves,
      ring_hom.finite_type_is_local.of_localization_span,
      ring_hom.finite_type_is_local] }
end

end algebraic_geometry
