/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import morphisms.finite
import morphisms.finite_type
import morphisms.universally_closed
import ring_theory.ring_hom.integral

/-!

# Integral morphisms

A morphism of schemes is integral if it is affine and the component of the sheaf map on integral opens
is integral.
We show that this property is local, and is stable under compositions and base-changes.

-/

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universe u

namespace algebraic_geometry

variables {X Y : Scheme.{u}} (f : X ⟶ Y)

lemma ring_hom.localization_is_integral :
  ring_hom.localization_preserves (λ R S _ _ f, by exactI f.is_integral) := sorry

lemma ring_hom.is_integral_of_localization_span :
  ring_hom.of_localization_span (λ R S _ _ f, by exactI f.is_integral) := sorry

/--
A morphism is `integral` if the preimages of integral open sets are integral.
-/
@[mk_iff]
class integral (f : X ⟶ Y) extends affine f : Prop :=
(is_integral_of_affine : ∀ U : opens Y.carrier, is_affine_open U → (f.1.c.app (op U)).is_integral)

def integral.affine_property : affine_target_morphism_property :=
affine_and (λ R S _ _ f, by exactI ring_hom.is_integral f)

lemma integral_eq_affine_property :
  @integral = target_affine_locally integral.affine_property :=
by { ext, rw [integral_iff, integral.affine_property,
  affine_and_target_affine_locally_iff ring_hom.is_integral_respects_iso] }

lemma integral.affine_property_is_local :
  integral.affine_property.is_local :=
is_local_affine_and _ ring_hom.is_integral_respects_iso ring_hom.localization_is_integral
  ring_hom.is_integral_of_localization_span

lemma integral_is_local_at_target :
  property_is_local_at_target @integral :=
integral_eq_affine_property.symm ▸ integral.affine_property_is_local.target_affine_locally_is_local

lemma integral_respects_iso : morphism_property.respects_iso @integral :=
integral_is_local_at_target.respects_iso

lemma integral_stable_under_composition : morphism_property.stable_under_composition @integral :=
by { rw integral_eq_affine_property, exact affine_and_stable_under_composition _
  ring_hom.is_integral_stable_under_composition }

lemma integral_stable_under_base_change : morphism_property.stable_under_base_change @integral :=
by { rw integral_eq_affine_property, exact affine_and_stable_under_base_change _
  ring_hom.is_integral_respects_iso ring_hom.localization_is_integral
  ring_hom.is_integral_of_localization_span
  ring_hom.is_integral_stable_under_base_change }

lemma integral_eq_affine_inf_universally_closed :
  @integral = @affine ⊓ @universally_closed :=
sorry

lemma finite_eq_integral_inf_locally_of_finite_type :
  @finite = @integral ⊓ @locally_of_finite_type :=
begin
  
end

@[priority 100]
instance universally_closed.to_integral {X Y : Scheme} (f : X ⟶ Y) [H : integral f] :
  universally_closed f :=
by { rw integral_eq_affine_inf_universally_closed at H, exact H.2 }

instance integral_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [integral f] [integral g] : integral (f ≫ g) :=
integral_stable_under_composition _ _ infer_instance infer_instance

-- lemma integral.affine_open_cover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
--   tfae [integral f,
--     ∃ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)],
--       ∀ (i : 𝒰.J), is_affine (pullback f (𝒰.map i)) ∧
--         ring_hom.integral (Scheme.Γ.map (pullback.snd : pullback f (𝒰.map i) ⟶ _).op),
--     ∀ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)] (i : 𝒰.J),
--       is_affine (pullback f (𝒰.map i)) ∧
--         ring_hom.integral (Scheme.Γ.map (pullback.snd : pullback f (𝒰.map i) ⟶ _).op),
--     ∀ {U : Scheme} (g : U ⟶ Y) [is_affine U] [is_open_immersion g],
--       is_affine (pullback f g) ∧
--         ring_hom.integral (Scheme.Γ.map (pullback.snd : pullback f g ⟶ _).op)] :=
-- integral_eq_affine_property.symm ▸
--   integral.affine_property_is_local.affine_open_cover_tfae f

-- lemma integral.open_cover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
--   tfae [integral f,
--     ∃ (𝒰 : Scheme.open_cover.{u} Y), ∀ (i : 𝒰.J),
--       integral (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
--     ∀ (𝒰 : Scheme.open_cover.{u} Y) (i : 𝒰.J),
--       integral (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
--     ∀ (U : opens Y.carrier), integral (f ∣_ U),
--     ∀ {U : Scheme} (g : U ⟶ Y) [is_open_immersion g],
--       integral (pullback.snd : pullback f g ⟶ _)] :=
-- affine_eq_affine_property.symm ▸
--   affine_affine_property_is_local.open_cover_tfae f

lemma integral_over_affine_iff [is_affine Y] :
  integral f ↔ is_affine X ∧ ring_hom.is_integral (Scheme.Γ.map f.op) :=
integral_eq_affine_property.symm ▸
  integral.affine_property_is_local.affine_target_iff f

lemma integral.affine_open_cover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.open_cover.{u} Y)
  [∀ i, is_affine (𝒰.obj i)] (f : X ⟶ Y) :
  integral f ↔ ∀ i, is_affine (pullback f (𝒰.map i)) ∧
    ring_hom.is_integral (Scheme.Γ.map (pullback.snd : pullback f (𝒰.map i) ⟶ _).op) :=
integral_eq_affine_property.symm ▸
  integral.affine_property_is_local.affine_open_cover_iff f 𝒰

lemma integral.open_cover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.open_cover.{u} Y)
  [∀ i, is_affine (𝒰.obj i)] (f : X ⟶ Y) :
  integral f ↔ ∀ i, integral (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
integral_eq_affine_property.symm ▸
  integral.affine_property_is_local.target_affine_locally_is_local.open_cover_iff f 𝒰

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [integral g] :
  integral (pullback.fst : pullback f g ⟶ X) :=
integral_stable_under_base_change (is_pullback.of_has_pullback f g).flip infer_instance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [integral f] :
  integral (pullback.snd : pullback f g ⟶ Y) :=
integral_stable_under_base_change (is_pullback.of_has_pullback f g) infer_instance

end algebraic_geometry