import morphisms.isomorphism
import algebraic_geometry.pullback_carrier

open opposite category_theory category_theory.limits topological_space

noncomputable theory

namespace algebraic_geometry

lemma injective_of_surjective_diagonal {X Y : Scheme} (f : X ⟶ Y)
  (h : function.surjective (pullback.diagonal f).1.base) : function.injective f.1.base :=
begin
  intros x y e,
  let T : pullback.triplet f f := ⟨x, y, _, e, rfl⟩,
  obtain ⟨z, hz, hz'⟩ := T.exists_preimage,
  obtain ⟨z', rfl⟩ := h z,
  simp only [← Scheme.comp_val_base_apply, pullback.diagonal_fst, pullback.diagonal_snd] at hz hz',
  exact hz.symm.trans hz'
end

lemma surjective_diagonal_of_universally_injective {X Y : Scheme} (f : X ⟶ Y)
  (h : function.surjective (pullback.diagonal f).1.base) : function.injective f.1.base :=
begin
  intros x y e,
  let T : pullback.triplet f f := ⟨x, y, _, e, rfl⟩,
  obtain ⟨z, hz, hz'⟩ := T.exists_preimage,
  obtain ⟨z', rfl⟩ := h z,
  simp only [← Scheme.comp_val_base_apply, pullback.diagonal_fst, pullback.diagonal_snd] at hz hz',
  exact hz.symm.trans hz'
end

lemma injective_of_mono {X Y : Scheme} (f : X ⟶ Y) [mono f] : 
  function.injective f.1.base :=
begin
  apply injective_of_surjective_diagonal,
  exact (as_iso $ (Scheme.forget_to_Top ⋙ forget Top).map
    (pullback.diagonal f)).to_equiv.surjective,
end

-- move me 
lemma mono_eq_diagonal : 
  @mono Scheme _ = morphism_property.diagonal (@is_iso Scheme _) :=
begin
  ext X Y f,
  split,
  { introI _, show is_iso _, apply_instance },
  { rintro (H : is_iso _),
    resetI,
  haveI : is_iso (pullback.fst : pullback f f ⟶ X),
  { rw (is_iso.inv_eq_of_hom_inv_id (pullback.diagonal_fst f)).symm, apply_instance },
  exact is_kernel_pair.mono_of_is_iso_fst (is_pullback.of_has_pullback f f) }
end

lemma mono_is_local_at_target : 
  property_is_local_at_target (@mono _ _) :=
begin
  rw mono_eq_diagonal,
  exact is_iso_is_local_at_target.diagonal
end

end algebraic_geometry