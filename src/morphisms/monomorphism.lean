import morphisms.basic
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

lemma injective_of_mono {X Y : Scheme} (f : X ⟶ Y) [mono f] : 
  function.injective f.1.base :=
begin
  apply injective_of_surjective_diagonal,
  exact (as_iso $ (Scheme.forget_to_Top ⋙ forget Top).map
    (pullback.diagonal f)).to_equiv.surjective,
end


end algebraic_geometry