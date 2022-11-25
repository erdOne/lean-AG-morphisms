/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import morphisms.quasi_separated
import morphisms.isomorphism

/-!

# Affine morphisms

A morphism of schemes is affine if the preimages of affine open sets are affine.

-/

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universe u

namespace algebraic_geometry

variables {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism is `affine` if the preimages of affine open sets are affine. -/
@[mk_iff]
class affine (f : X ⟶ Y) : Prop :=
(is_affine_preimage : ∀ U : opens Y.carrier,
  is_affine_open U → is_affine_open ((opens.map f.1.base).obj U))

/-- The `affine_target_morphism_property` corresponding to affine morphisms. -/
def affine.affine_property : affine_target_morphism_property :=
λ X Y f hf, is_affine X

@[simp] lemma affine_affine_property_to_property {X Y : Scheme} (f : X ⟶ Y) :
  affine_target_morphism_property.to_property affine.affine_property f ↔
    is_affine Y ∧ is_affine X :=
by { delta affine_target_morphism_property.to_property affine.affine_property, simp }

@[priority 900]
instance affine_of_is_iso {X Y : Scheme} (f : X ⟶ Y) [is_iso f] : affine f :=
⟨λ U hU, hU.map_is_iso f⟩

@[priority 100]
instance affine.to_quasi_compact [affine f] : quasi_compact f :=
(quasi_compact_iff_forall_affine f).mpr (λ U hU, (affine.is_affine_preimage U hU).is_compact)

instance affine_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [affine f] [affine g] : affine (f ≫ g) :=
begin
  constructor,
  intros U hU,
  rw [Scheme.comp_val_base, opens.map_comp_obj],
  apply affine.is_affine_preimage,
  apply affine.is_affine_preimage,
  exact hU
end

lemma affine_iff_affine_property :
  affine f ↔ target_affine_locally affine.affine_property f :=
(affine_iff f).trans ⟨λ H U, H U U.prop, λ H U hU, H ⟨U, hU⟩⟩

lemma affine_eq_affine_property :
  @affine = target_affine_locally affine.affine_property :=
by { ext, exact affine_iff_affine_property _ }

instance {X : Scheme} (r : X.presheaf.obj (op ⊤)) :
  affine (X.of_restrict (X.basic_open r).open_embedding) :=
begin
  constructor,
  intros U hU,
  fapply (is_affine_open_iff_of_is_open_immersion (X.of_restrict _) _).mp,
  swap,
  { apply_instance },
  convert hU.basic_open_is_affine (X.presheaf.map (hom_of_le le_top).op r),
  rw X.basic_open_res,
  ext1,
  refine set.image_preimage_eq_inter_range.trans _,
  erw subtype.range_coe,
  refl
end

/-- The preimage of an affine open as an `Scheme.affine_opens`. -/
@[simps]
def affine_preimage {X Y : Scheme} (f : X ⟶ Y) [affine f] (U : Y.affine_opens) :
  X.affine_opens :=
⟨(opens.map f.1.base).obj (U : opens Y.carrier), affine.is_affine_preimage _ U.prop⟩

lemma is_affine_of_span_top_of_is_affine_open (X : Scheme) (s : set (X.presheaf.obj $ op ⊤))
  (h₁ : ideal.span s = ⊤) (h₂ : ∀ r : s, is_affine_open (X.basic_open r.1)) : is_affine X :=
begin
  haveI hX' : quasi_separated_space X.carrier,
  { obtain ⟨s', hs', e⟩ := (ideal.span_eq_top_iff_finite _).mp h₁,
    rw quasi_separated_space_iff_affine,
    intros U V,
    rw [← set.inter_univ (U ∩ V : set X.carrier), ← (show _ = set.univ, from
      (congr_arg subtype.val $ supr_basic_open_eq_top_of_span_eq_top _ _ e : _)), opens.supr_def,
      subtype.val_eq_coe, subtype.coe_mk, set.inter_Union],
    apply is_compact_Union,
    intro i,
    convert_to is_compact ((U.1 ⊓ (X.basic_open i.val)) ⊓ (V.1 ⊓ (X.basic_open i.val))).1,
    { conv_rhs { rw [inf_assoc, ← @inf_assoc _ _ (X.basic_open i.1),
        @inf_comm _ _ (X.basic_open i.1), inf_assoc, inf_idem, ← inf_assoc] },
      refl },
    have : ∀ (S : opens X.carrier), S ⊓ X.basic_open i.1 = X.basic_open
      (X.presheaf.map (hom_of_le le_top : S ⟶ _).op i.1) := λ S, (X.basic_open_res _ _).symm,
    apply (h₂ ⟨i.1, hs' i.2⟩).is_quasi_separated,
    { exact @inf_le_right _ _ U.1 _ },
    { exact (U.val ⊓ X.basic_open i.val).2 },
    { rw this, exact (U.prop.basic_open_is_affine _).is_compact },
    { exact @inf_le_right _ _ V.1 _ },
    { exact (V.val ⊓ X.basic_open i.val).2 },
    { rw this, exact (V.prop.basic_open_is_affine _).is_compact } },
  have hX : compact_space X.carrier,
  { obtain ⟨s', hs', e⟩ := (ideal.span_eq_top_iff_finite _).mp h₁,
    rw [← is_compact_univ_iff, ← (show _ = set.univ, from
      (congr_arg subtype.val $ supr_basic_open_eq_top_of_span_eq_top _ _ e : _)), opens.supr_def],
    apply is_compact_Union,
    intro i, exact (h₂ ⟨i.1, hs' i.2⟩).is_compact },
  constructor,
  rw (is_iso.open_cover_tfae (Γ_Spec.adjunction.unit.app X)).out 0 5,
  refine ⟨s, λ i, prime_spectrum.basic_open i.1, _, _⟩,
  { rw prime_spectrum.Union_basic_open_eq_top_iff, convert h₁, simp },
  { intro r,
    apply_with is_iso_of_is_affine_is_iso { instances := ff },
    { change is_affine_open _,
      rw preimage_adjunction_unit_basic_open,
      exact h₂ r },
    { change is_affine_open _,
      rw ← basic_open_eq_of_affine,
      apply is_affine_open.basic_open_is_affine,
      apply_with top_is_affine_open { instances := ff },
      exact algebraic_geometry.Spec_is_affine _ },
    { suffices : ∀ (U = prime_spectrum.basic_open r.val),
        is_iso ((Γ_Spec.adjunction.unit.app X).val.c.app (op $ U)),
      { rw morphism_restrict_c_app,
        apply_with is_iso.comp_is_iso { instances := ff },
        { apply this, rw opens.open_embedding_obj_top },
        { apply_instance } },
      rintros _ rfl,
      rw CommRing.is_iso_iff_bijective,
      fapply bijective_of_is_localization (submonoid.powers r.1),
      rotate,
      { apply structure_sheaf.open_algebra },
      { apply ring_hom.to_algebra,
        exact X.presheaf.map (hom_of_le le_top :
          (opens.map (Γ_Spec.adjunction.unit.app X).val.base).obj _ ⟶ _).op },
      { apply structure_sheaf.is_localization.to_basic_open },
      { dsimp,
        rw ← is_compact_univ_iff at hX,
        rw ← is_quasi_separated_univ_iff at hX',
        convert is_localization_basic_open_of_qcqs
          (show is_compact (⊤ : opens _).1, from hX) hX' r.1;
          apply Γ_Spec.adjunction.unit_app_map_basic_open },
      { rw [ring_hom.algebra_map_to_algebra, ring_hom.algebra_map_to_algebra,
          Γ_Spec.adjunction_unit_app],
        exact X.1.to_Γ_Spec_SheafedSpace_app_spec r.1 } } }
end

lemma affine_affine_property_is_local :
  affine_target_morphism_property.is_local affine.affine_property :=
begin
  split,
  { apply affine_target_morphism_property.respects_iso_mk,
    all_goals { rintros X Y Z _ _ _ (H : is_affine _), resetI },
    exacts [is_affine_of_iso e.hom, H] },
  { introv H,
    change is_affine_open _,
    rw Scheme.preimage_basic_open f r,
    exact (@@top_is_affine_open X H).basic_open_is_affine _ },
  { rintros X Y H f S hS hS',
    resetI,
    apply_fun ideal.map (f.1.c.app (op ⊤)) at hS,
    rw [ideal.map_span, ideal.map_top] at hS,
    delta affine.affine_property,
    unfreezingI { change ∀ (i : S), is_affine_open _ at hS',
      simp_rw Scheme.preimage_basic_open at hS' },
    apply is_affine_of_span_top_of_is_affine_open X _ hS,
    rintro ⟨_, r, hr, rfl⟩,
    exact hS' ⟨r, hr⟩ }
end

lemma affine_affine_property_stable_under_base_change :
  affine_target_morphism_property.stable_under_base_change affine.affine_property :=
begin
  introv X H,
  delta affine.affine_property at H ⊢,
  resetI,
  apply_instance
end

lemma affine_over_affine_iff {X Y : Scheme} (f : X ⟶ Y) [is_affine Y] :
  affine f ↔ is_affine X :=
affine_eq_affine_property.symm ▸
  affine_affine_property_is_local.affine_target_iff f

@[priority 100]
instance affine_of_is_affine [is_affine X] [is_affine Y] : affine f :=
begin
  rw affine_over_affine_iff,
  apply_instance
end

lemma is_affine_of_affine [affine f] [is_affine Y] : is_affine X :=
begin
  rw ← affine_over_affine_iff f,
  apply_instance
end

end algebraic_geometry
