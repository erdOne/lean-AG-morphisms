import morphisms.basic
import algebraic_geometry.pullback_carrier

/-!
# Surjective morphisms

A morphism of schemes `f : X ⟶ Y` is surjective if the underlying map is.

-/

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universe u

open_locale algebraic_geometry

namespace algebraic_geometry

variables {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/- A morphism of schemes `f : X ⟶ Y` is surjective if the underlying map is. -/
@[mk_iff]
class surjective (f : X ⟶ Y) : Prop :=
(out [] : function.surjective f.1.base)

instance surjective_of_is_iso [is_iso f] : surjective f :=
⟨(Top.homeo_of_iso $ as_iso f.1.base).surjective⟩

lemma surjective_stable_under_composition :
  morphism_property.stable_under_composition @surjective :=
λ X Y Z f g hf hg, ⟨hg.out.comp hf.out⟩

lemma surjective_respects_iso : 
  morphism_property.respects_iso @surjective :=
surjective_stable_under_composition.respects_iso (λ X Y f, infer_instance)

lemma surjective_stable_under_base_change : 
  morphism_property.stable_under_base_change @surjective :=
morphism_property.stable_under_base_change.mk surjective_respects_iso 
begin
  intros X Y S f g H,
  rw surjective_iff at H ⊢,
  rw [← set.range_iff_surjective, pullback.range_fst, set.range_iff_surjective.mpr H],
  refl
end

lemma surjective_is_local_at_target :
  property_is_local_at_target @surjective :=
begin
  refine ⟨surjective_respects_iso, _, _⟩,
  { intros X Y f U H,
    rw surjective_iff at H ⊢, 
    rw morphism_restrict_val_base,
    exact set.restrict_preimage_surjective _ H },
  { intros X Y f 𝒰 H,
    rw surjective_iff,
    have : (⋃ i, (𝒰.map i).opens_range.1) = set.univ,
    { rw [← opens.coe_top, ← 𝒰.supr_opens_range, opens.coe_supr], refl },
    refine (set.surjective_iff_surjective_of_Union_eq_univ this).mpr (λ i, _),
    rw [← morphism_restrict_val_base, ← surjective_iff, 
      surjective_respects_iso.arrow_mk_iso_iff
      (morphism_restrict_opens_range _ _)],
    exact H _ }
end

end algebraic_geometry