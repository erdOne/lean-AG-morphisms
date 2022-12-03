/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import morphisms.open_immersion

/-!

# Open immersions

A morphism is an open immersions if the underlying map of spaces is an open embedding
`f : X ⟶ U ⊆ Y`, and the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.

Most of the theories are developed in `algebraic_geometry/open_immersion`, and we provide the
remaining theorems analogous to other lemmas in `algebraic_geometry/morphisms/*`.

-/

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universe u

namespace algebraic_geometry

variables {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

lemma is_iso_iff_stalk {f : X ⟶ Y} :
  is_iso f ↔
    is_iso f.1.base ∧ ∀ x, is_iso (PresheafedSpace.stalk_map f.1 x) :=
begin
  split,
  { intro h, exactI ⟨infer_instance, infer_instance⟩ },
  { rintro ⟨h₁, h₂⟩, resetI,
    haveI := is_open_immersion.of_stalk_iso f (Top.homeo_of_iso $ as_iso f.1.base).open_embedding,
    exact is_open_immersion.to_iso f }
end

lemma is_iso_respects_iso : morphism_property.respects_iso (@is_iso Scheme _) :=
by split; { introv H, resetI, apply_instance }

lemma is_iso_is_local_at_target : property_is_local_at_target (@is_iso Scheme _) :=
begin
  constructor,
  { exact is_iso_respects_iso },
  { introsI, apply_instance },
  { introsI X Y f 𝒰 H,
    haveI := is_open_immersion_is_local_at_target.3 f 𝒰 infer_instance,
    suffices : function.surjective f.1.base,
    { rw ← Top.epi_iff_surjective f.1.base at this, exactI is_open_immersion.to_iso f },
    have := congr_arg (coe : opens Y.carrier → set Y.carrier) 𝒰.supr_opens_range,
    rw opens.coe_supr at this,
    rw set.surjective_iff_surjective_of_Union_eq_univ this,
    intro i,
    haveI := (is_iso_respects_iso.arrow_iso_iff
      (morphism_restrict_opens_range f (𝒰.map i))).mpr (H i),
    have : epi (arrow.mk (f ∣_ Scheme.hom.opens_range (𝒰.map i))).hom.1.base := infer_instance,
    rw [Top.epi_iff_surjective, arrow.mk_hom, morphism_restrict_val_base] at this,
    exact this }
end

lemma is_iso.open_cover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
  tfae [is_iso f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y), ∀ (i : 𝒰.J),
      is_iso (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (𝒰 : Scheme.open_cover.{u} Y) (i : 𝒰.J),
      is_iso (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (U : opens Y.carrier), is_iso (f ∣_ U),
    ∀ {U : Scheme} (g : U ⟶ Y) [is_open_immersion g],
      is_iso (pullback.snd : pullback f g ⟶ U),
    ∃ {ι : Type u} (U : ι → opens Y.carrier) (hU : supr U = ⊤),
      ∀ i, is_iso (f ∣_ (U i))] :=
is_iso_is_local_at_target.open_cover_tfae f

lemma is_iso_of_is_affine_is_iso {X Y : Scheme} [hX : is_affine X] [hY : is_affine Y] (f : X ⟶ Y)
  [hf : is_iso (f.1.c.app (op ⊤))] : is_iso f :=
begin
  rw ← mem_Spec_ess_image at hX hY,
  have : is_iso (AffineScheme.Γ.map (@quiver.hom.op AffineScheme _ ⟨X, hX⟩ ⟨Y, hY⟩ f)) := hf,
  have := @@is_iso_of_reflects_iso _ _ _ _ this _,
  exact @@functor.map_is_iso _ _ AffineScheme.forget_to_Scheme _ (@@is_iso_of_op _ _ this)
end

lemma target_affine_locally_affine_and_is_iso :
  target_affine_locally (λ X Y f hY, is_affine X ∧ is_iso (Scheme.Γ.map f.op)) = @is_iso Scheme _ :=
begin
  rw ← is_iso_is_local_at_target.target_affine_locally_eq,
  congr,
  ext X Y f hY,
  split,
  { rintros ⟨hX, hf⟩, exactI @@is_iso_of_is_affine_is_iso _ _ f hf },
  { intro hf, exactI ⟨is_affine_of_iso f, infer_instance⟩ }
end

end algebraic_geometry