/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import morphisms.closed_immersion
import ring_theory.ring_hom.finite
import ring_theory.local_properties
import for_mathlib.epi_finite

/-!

# Finite morphisms

A morphism of schemes is finite if it is affine and the component of the sheaf map on finite opens
is finite.
We show that this property is local, and is stable under compositions and base-changes.

-/

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universe u

namespace algebraic_geometry

variables {X Y : Scheme.{u}} (f : X ⟶ Y)

/--
A morphism is `finite` if the preimages of finite open sets are finite.
-/
@[mk_iff]
class finite (f : X ⟶ Y) extends affine f : Prop :=
(is_finite_of_affine : ∀ U : opens Y.carrier, is_affine_open U → (f.1.c.app (op U)).finite)

def finite.affine_property : affine_target_morphism_property :=
affine_and @ring_hom.finite

lemma finite_eq_affine_property :
  @finite = target_affine_locally finite.affine_property :=
by { ext, rw [finite_iff, finite.affine_property,
  affine_and_target_affine_locally_iff ring_hom.finite_respects_iso] }

lemma finite.affine_property_is_local :
  finite.affine_property.is_local :=
is_local_affine_and _ ring_hom.finite_respects_iso localization_finite finite_of_localization_span

lemma finite_is_local_at_target :
  property_is_local_at_target @finite :=
finite_eq_affine_property.symm ▸ finite.affine_property_is_local.target_affine_locally_is_local

lemma finite_respects_iso : morphism_property.respects_iso @finite :=
finite_is_local_at_target.respects_iso

lemma finite_stable_under_composition : morphism_property.stable_under_composition @finite :=
by { rw finite_eq_affine_property, exact affine_and_stable_under_composition @ring_hom.finite
  ring_hom.finite_stable_under_composition }

lemma finite_stable_under_base_change : morphism_property.stable_under_base_change @finite :=
by { rw finite_eq_affine_property, exact affine_and_stable_under_base_change _
  ring_hom.finite_respects_iso localization_finite finite_of_localization_span
  ring_hom.finite_stable_under_base_change }

lemma finite_le_affine : @finite ≤ @affine :=
by { rw finite_eq_affine_property, exact target_affine_locally_affine_and_le_affine _ }

-- move me
lemma _root_.category_theory.morphism_property.respects_iso.inf {C} [category C]
  {P₁ P₂ : morphism_property C} (h₁ : P₁.respects_iso) (h₂ : P₂.respects_iso) :
    (P₁ ⊓ P₂).respects_iso :=
⟨λ _ _ _ _ _ ⟨H₁, H₂⟩, ⟨h₁.1 _ _ H₁, h₂.1 _ _ H₂⟩,
    λ _ _ _ _ _ ⟨H₁, H₂⟩, ⟨h₁.2 _ _ H₁, h₂.2 _ _ H₂⟩⟩

-- move me
lemma property_is_local_at_target.inf {P₁ P₂} (h₁ : property_is_local_at_target P₁)
  (h₂ : property_is_local_at_target P₂) : property_is_local_at_target (P₁ ⊓ P₂) :=
⟨h₁.1.inf h₂.1, λ X Y f U H, ⟨h₁.2 _ _ H.1, h₂.2 _ _ H.2⟩, λ X Y f 𝒰 H,
  ⟨h₁.3 _ 𝒰 $ λ i, (H i).1, h₂.3 _ 𝒰 $ λ i, (H i).2⟩⟩

lemma finite_Spec_iff {R S : CommRing} (f : R ⟶ S) :
  finite (Scheme.Spec.map f.op) ↔ ring_hom.finite f :=
begin
  rw [finite_eq_affine_property,
    finite.affine_property_is_local.affine_target_iff,
    finite.affine_property, affine_and_Spec_iff ring_hom.finite_respects_iso]
end

lemma is_closed_immersion_eq_finite_inf_mono :
  @is_closed_immersion = @finite ⊓ @mono Scheme _ :=
begin
  apply property_ext_of_le_affine is_closed_immersion_le_affine
    (inf_le_left.trans finite_le_affine) is_closed_immersion.is_local_at_target
    (finite_is_local_at_target.inf mono_is_local_at_target),
  intros R S f,
  simp_rw [is_closed_immersion_Spec_iff, pi.inf_apply, finite_Spec_iff],
  split,
  { rintro H,
    haveI := (is_closed_immersion_Spec_iff _).mpr H,
    exact ⟨ring_hom.finite.of_surjective _ H, infer_instance⟩ },
  { rintro ⟨h₁, h₂⟩,
    rw functor.mono_map_iff_mono at h₂,
    resetI,
    refine ring_hom.surjective_of_epi_of_finite _ _ h₁,
    convert @@category_theory.unop_epi_of_mono _ f.op h₂; exact CommRing.of_eq _ }
end

@[priority 100]
instance is_closed_immerison.to_finite {X Y : Scheme} (f : X ⟶ Y) [H : is_closed_immersion f] :
  finite f :=
by { rw is_closed_immersion_eq_finite_inf_mono at H, exact H.1 }

instance finite_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [finite f] [finite g] : finite (f ≫ g) :=
finite_stable_under_composition _ _ infer_instance infer_instance

-- lemma finite.affine_open_cover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
--   tfae [finite f,
--     ∃ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)],
--       ∀ (i : 𝒰.J), is_affine (pullback f (𝒰.map i)) ∧
--         ring_hom.finite (Scheme.Γ.map (pullback.snd : pullback f (𝒰.map i) ⟶ _).op),
--     ∀ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)] (i : 𝒰.J),
--       is_affine (pullback f (𝒰.map i)) ∧
--         ring_hom.finite (Scheme.Γ.map (pullback.snd : pullback f (𝒰.map i) ⟶ _).op),
--     ∀ {U : Scheme} (g : U ⟶ Y) [is_affine U] [is_open_immersion g],
--       is_affine (pullback f g) ∧
--         ring_hom.finite (Scheme.Γ.map (pullback.snd : pullback f g ⟶ _).op)] :=
-- finite_eq_affine_property.symm ▸
--   finite.affine_property_is_local.affine_open_cover_tfae f

-- lemma finite.open_cover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
--   tfae [finite f,
--     ∃ (𝒰 : Scheme.open_cover.{u} Y), ∀ (i : 𝒰.J),
--       finite (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
--     ∀ (𝒰 : Scheme.open_cover.{u} Y) (i : 𝒰.J),
--       finite (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
--     ∀ (U : opens Y.carrier), finite (f ∣_ U),
--     ∀ {U : Scheme} (g : U ⟶ Y) [is_open_immersion g],
--       finite (pullback.snd : pullback f g ⟶ _)] :=
-- affine_eq_affine_property.symm ▸
--   affine_affine_property_is_local.open_cover_tfae f

lemma finite_over_affine_iff [is_affine Y] :
  finite f ↔ is_affine X ∧ ring_hom.finite (Scheme.Γ.map f.op) :=
finite_eq_affine_property.symm ▸
  finite.affine_property_is_local.affine_target_iff f

lemma finite.affine_open_cover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.open_cover.{u} Y)
  [∀ i, is_affine (𝒰.obj i)] (f : X ⟶ Y) :
  finite f ↔ ∀ i, is_affine (pullback f (𝒰.map i)) ∧
    ring_hom.finite (Scheme.Γ.map (pullback.snd : pullback f (𝒰.map i) ⟶ _).op) :=
finite_eq_affine_property.symm ▸
  finite.affine_property_is_local.affine_open_cover_iff f 𝒰

lemma finite.open_cover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.open_cover.{u} Y)
  [∀ i, is_affine (𝒰.obj i)] (f : X ⟶ Y) :
  finite f ↔ ∀ i, finite (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
finite_eq_affine_property.symm ▸
  finite.affine_property_is_local.target_affine_locally_is_local.open_cover_iff f 𝒰

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [finite g] :
  finite (pullback.fst : pullback f g ⟶ X) :=
finite_stable_under_base_change (is_pullback.of_has_pullback f g).flip infer_instance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [finite f] :
  finite (pullback.snd : pullback f g ⟶ Y) :=
finite_stable_under_base_change (is_pullback.of_has_pullback f g) infer_instance

end algebraic_geometry