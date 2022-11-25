/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import morphisms.immersion
import for_mathlib.pullback_lift_comp

/-!
# Separated morphisms

A morphism of schemes `f : X ⟶ Y` is separated if the diagonal morphism `X ⟶ X ×[Y] X` is
a closed immersion.

-/

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universe u

open_locale algebraic_geometry

namespace algebraic_geometry

variables {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism is `separated` if diagonal map is a closed immersion. -/
@[mk_iff]
class separated (f : X ⟶ Y) : Prop :=
(diagonal_is_closed_immersion : is_closed_immersion (pullback.diagonal f))

attribute [instance] separated.diagonal_is_closed_immersion

/-- A scheme is separated if it is separated over `Spec ℤ`. -/
@[mk_iff]
class is_separated (X : Scheme) : Prop :=
(out : separated (terminal.from X))

attribute [instance] is_separated.out

lemma separated_eq_diagonal_is_is_closed_immersion :
  @separated = morphism_property.diagonal @is_closed_immersion :=
by { ext, exact separated_iff _ }

lemma separated_eq_affine_property_diagonal :
  @separated =
    target_affine_locally is_closed_immersion.affine_property.diagonal :=
begin
  rw [separated_eq_diagonal_is_is_closed_immersion, is_closed_immersion_eq_affine_property],
  exact diagonal_target_affine_locally_eq_target_affine_locally
    _ is_closed_immersion.affine_property_is_local
end

@[priority 100]
instance separated_of_mono [mono f] : separated f :=
⟨infer_instance⟩

@[priority 100]
instance separated.to_quasi_separated [separated f] : quasi_separated f := ⟨infer_instance⟩

lemma separated_stable_under_composition :
  morphism_property.stable_under_composition @separated :=
separated_eq_diagonal_is_is_closed_immersion.symm ▸
  is_closed_immersion_stable_under_composition.diagonal
    is_closed_immersion_respects_iso
    is_closed_immersion_stable_under_base_change

lemma separated_stable_under_base_change :
  morphism_property.stable_under_base_change @separated :=
separated_eq_diagonal_is_is_closed_immersion.symm ▸
  is_closed_immersion_stable_under_base_change.diagonal
    is_closed_immersion_respects_iso

instance separated_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [separated f] [separated g] : separated (f ≫ g) :=
separated_stable_under_composition f g infer_instance infer_instance

lemma separated_respects_iso : morphism_property.respects_iso @separated :=
separated_eq_diagonal_is_is_closed_immersion.symm ▸
  is_closed_immersion_respects_iso.diagonal

lemma separated.is_local_at_target :
  property_is_local_at_target @separated :=
separated_eq_affine_property_diagonal.symm ▸
  is_closed_immersion.affine_property_is_local.diagonal.target_affine_locally_is_local

lemma separated.open_cover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
  tfae [separated f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y), ∀ (i : 𝒰.J),
      separated (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (𝒰 : Scheme.open_cover.{u} Y) (i : 𝒰.J),
      separated (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (U : opens Y.carrier), separated (f ∣_ U),
    ∀ {U : Scheme} (g : U ⟶ Y) [is_open_immersion g],
      separated (pullback.snd : pullback f g ⟶ _),
    ∃ {ι : Type u} (U : ι → opens Y.carrier) (hU : supr U = ⊤),
      ∀ i, separated (f ∣_ (U i))] :=
separated.is_local_at_target.open_cover_tfae f

lemma affine_le_separated : 
  @affine ≤ @separated :=
begin
  rw [affine_eq_affine_property, ← separated.is_local_at_target.target_affine_locally_eq],
  apply target_affine_locally_mono,
  rintros X Y f H (hf : is_affine X),
  resetI,
  rw [← separated_respects_iso.cancel_right_is_iso _ (Γ_Spec.adjunction.unit.app Y), 
    ← Γ_Spec.adjunction.unit_naturality f, separated_respects_iso.cancel_left_is_iso,
    functor.right_op_map],
  exact ⟨is_closed_immersion_pullback_diagonal_Spec (Scheme.Spec.map (Scheme.Γ.map f.op).op)⟩
end

@[priority 100]
instance affine.to_separated [affine f] : separated f := affine_le_separated _ _ _ infer_instance

lemma is_closed_immersion.of_comp_of_is_immersion [is_closed_immersion (f ≫ g)] [is_immersion g] :
  is_closed_immersion f :=
begin
  haveI := is_immersion.of_comp_of_is_immersion f g,
  apply is_closed_immersion.of_is_immersion,
  rw [← set.preimage_image_eq (set.range _) (is_immersion.base_embedding g).inj,
    ← set.range_comp, ← coe_comp, ← Scheme.comp_val_base],
  exact (is_closed_immersion.base_closed $ f ≫ g).2.preimage g.1.base.2,
end

lemma separated_of_comp {Z : Scheme} (g : Y ⟶ Z) [H : separated (f ≫ g)] : separated f :=
begin
  constructor,
  apply_with is_closed_immersion.of_comp_of_is_immersion { instances := ff },
  { rwa [separated_iff, pullback.diagonal_comp] at H },
  rw [is_immersion_respects_iso.cancel_left_is_iso],
  apply_instance
end

@[priority 100]
instance is_affine.to_is_separated [is_affine X] : is_separated X := ⟨infer_instance⟩

lemma separated_of_comp_iff {Z : Scheme} (g : Y ⟶ Z) [separated g] :
  separated (f ≫ g) ↔ separated f :=
⟨λ h, by exactI separated_of_comp f g, λ h, by exactI infer_instance⟩

lemma separated_over_is_separated_iff [is_separated Y] :
  separated f ↔ is_separated X :=
by { rw [is_separated_iff, ← terminal.comp_from f], exact (separated_of_comp_iff _ _).symm }

@[priority 100]
instance separated.of_is_separated [is_separated X] : separated f := 
@@separated_of_comp f (terminal.from Y) (by { rw terminal.comp_from, apply_instance })

lemma is_separated_of_separated [is_separated Y] [separated f] : is_separated X :=
begin
  rw [is_separated_iff, ← terminal.comp_from f], 
  apply_instance
end

-- lemma separated.affine_open_cover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.open_cover.{u} Y)
--   [∀ i, is_affine (𝒰.obj i)] (f : X ⟶ Y) :
--   separated f ↔ ∀ i, is_separated (pullback f (𝒰.map i)) :=
-- begin
--   rw [separated_eq_affine_property,
--     separated.affine_property_is_local.affine_open_cover_iff f 𝒰],
--   refl,
-- end

lemma separated.open_cover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.open_cover.{u} Y)
  (f : X ⟶ Y) :
  separated f ↔ ∀ i, separated (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
separated.is_local_at_target.open_cover_iff f 𝒰

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [separated g] :
  separated (pullback.fst : pullback f g ⟶ X) :=
separated_stable_under_base_change.fst f g infer_instance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [separated f] :
  separated (pullback.snd : pullback f g ⟶ Y) :=
separated_stable_under_base_change.snd f g infer_instance

instance {X Y Z: Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [separated f] [separated g] :
  separated (f ≫ g) :=
separated_stable_under_composition f g infer_instance infer_instance

instance {S T : Scheme} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) :
  is_immersion (pullback.map_desc f g i) :=
is_immersion_stable_under_base_change (pullback_map_diagonal_is_pullback f g i) infer_instance

instance {S T : Scheme} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [separated i] :
  is_closed_immersion (pullback.map_desc f g i) :=
is_closed_immersion_stable_under_base_change (pullback_map_diagonal_is_pullback f g i)
  infer_instance

instance {S T : Scheme} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [quasi_separated i] :
  quasi_compact (pullback.map_desc f g i) :=
quasi_compact_stable_under_base_change (pullback_map_diagonal_is_pullback f g i)
  infer_instance

lemma is_affine_open.inter [is_separated X] {U V : opens X.carrier} (hU : is_affine_open U)
  (hV : is_affine_open V) : is_affine_open (U ⊓ V) :=
begin
  haveI : is_affine _ := hU,
  haveI : is_affine _ := hV,
  haveI : is_affine (pullback (X.of_restrict U.open_embedding) (X.of_restrict V.open_embedding)),
  { apply is_affine_of_affine (pullback.map_desc (X.of_restrict U.open_embedding)
      (X.of_restrict V.open_embedding) (terminal.from X)) },
  have : (pullback (X.of_restrict U.open_embedding) (X.of_restrict V.open_embedding)) ≅ 
    X.restrict (U ⊓ V).open_embedding,
  { refine is_open_immersion.iso_of_range_eq (pullback.fst ≫ X.of_restrict _) (X.of_restrict _) _,
    simp_rw [is_open_immersion.range_pullback_to_base_of_left, Scheme.of_restrict_val_base,
      opens.range_inclusion], refl },
  exact is_affine_of_iso this.inv
end

instance : is_immersion (pullback.lift_comp f g) :=
begin
  rw is_immersion_respects_iso.arrow_mk_iso_iff (pullback.lift_comp_iso_map_desc f g),
  apply_instance
end

instance [separated g] : is_closed_immersion (pullback.lift_comp f g) :=
begin
  rw is_closed_immersion_respects_iso.arrow_mk_iso_iff (pullback.lift_comp_iso_map_desc f g),
  apply_instance
end

instance [quasi_separated g] : quasi_compact (pullback.lift_comp f g) :=
begin
  rw quasi_compact_respects_iso.arrow_mk_iso_iff (pullback.lift_comp_iso_map_desc f g),
  apply_instance
end

instance is_immersion_of_is_split_mono [is_split_mono f] : is_immersion f :=
begin
  have : pullback.map_desc f (𝟙 _) (retraction f) ≫ pullback.snd = pullback.fst ≫ f,
  { rw [pullback.lift_snd, pullback.condition] },
  rw ← is_iso.inv_comp_eq at this,
  rw ← this,
  haveI : is_iso (f ≫ retraction f) := by { rw is_split_mono.id, apply_instance },
  apply_instance
end

lemma quasi_compact_of_comp [quasi_compact (f ≫ g)] [quasi_separated g] : quasi_compact f :=
begin
  rw ← pullback.lift_comp_snd f g,
  apply_instance
end

lemma is_immersion_of_comp [is_immersion (f ≫ g)] : is_immersion f :=
begin
  rw ← pullback.lift_comp_snd f g,
  apply_instance
end

lemma is_closed_immersion_of_comp [is_immersion (f ≫ g)] [separated f] : is_immersion f :=
begin
  rw ← pullback.lift_comp_snd f g,
  apply_instance
end

end algebraic_geometry
