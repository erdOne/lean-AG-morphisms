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

--move me
def Spec_Γ_arrow_iso_of_is_affine [is_affine X] [is_affine Y] :
  arrow.mk f ≅ arrow.mk (Scheme.Spec.map (Scheme.Γ.map f.op).op) :=
arrow.iso_mk' _ _ (as_iso $ Γ_Spec.adjunction.unit.app _) (as_iso $ Γ_Spec.adjunction.unit.app _)
  (Γ_Spec.adjunction.unit_naturality f)

--move me
def Γ_Spec_arrow_iso {R S : CommRing} (f : R ⟶ S) :
  arrow.mk f ≅ arrow.mk (Scheme.Γ.map (Scheme.Spec.map f.op).op) :=
(arrow.iso_of_nat_iso Spec_Γ_identity (arrow.mk f)).symm

lemma is_closed_immersion_eq_finite_inf_mono :
  @is_closed_immersion = @finite ⊓ @mono Scheme _ :=
begin
  rw [is_closed_immersion_eq_affine_property, finite_eq_affine_property,
    ← mono_is_local_at_target.target_affine_locally_eq, ← target_affine_locally_and],
  congr' 1,
  ext X Y f,
  resetI,
  split,
  { rintro ⟨h₁, h₂⟩,
    haveI := (is_closed_immersion_over_affine_iff f).mpr ⟨h₁, h₂⟩,
    refine ⟨⟨h₁, ring_hom.finite.of_surjective _ h₂⟩, infer_instance⟩ },
  { rintro ⟨⟨h₁, h₂⟩, h₃⟩,
    resetI,
    rw mono_is_local_at_target.respects_iso.arrow_mk_iso_iff
      (Spec_Γ_arrow_iso_of_is_affine f) at h₃,
    refine ⟨h₁, ring_hom.surjective_of_epi_of_finite _ _ h₂⟩,
    convert @@category_theory.unop_epi_of_mono _ (Scheme.Γ.map f.op).op
      (Scheme.Spec.mono_of_mono_map h₃); exact CommRing.of_eq _ }
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