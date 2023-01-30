import morphisms.surjective

/-!
# Radicial morphisms

A morphism of schemes `f : X ⟶ Y` is radicial if the underlying map is injective,
and it induces radicial (purely inseparable) extensions on residue fields.

-/

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universe u

open_locale algebraic_geometry

namespace algebraic_geometry

variables {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- 
A field extension is radicial if it is an epi in the category of fields.

TODO: Replace this with purely inseparable extensions once we have those.
-/
def _root_.ring_hom.is_radicial {K L : Type u} [field K] [field L] (f : K →+* L) : Prop :=
∀ (L' : Type u) [field L'],
  by exactI function.injective (flip ring_hom.comp f : (L →+* L') → (K →+* L'))

/--
A morphism of schemes `f : X ⟶ Y` is radicial if the underlying map is injective,
and it induces radicial (purely inseparable) extensions on residue fields.

We show that this is equivalent to universally injective and equivalent to the diagonal map being
surjective below.
-/
@[mk_iff]
class radicial (f : X ⟶ Y) : Prop :=
(base_injective [] : function.injective f.1.base)
(residue_radicial [] : ∀ x, ring_hom.is_radicial (f.map_residue_field x))

section tfae

lemma radicial.epi_of_field [radicial f] {K : Type*} [field K] : 
  function.injective (λ g : Scheme.Spec.obj (op $ CommRing.of K) ⟶ X, g ≫ f) :=
begin
  intros g₁ g₂ e,
  dsimp only at e,
  apply (Spec_to_equiv_of_field K _).injective,
  refine Spec_to_equiv_of_field_eq_iff.mpr ⟨_, _⟩,
  { apply radicial.base_injective f,
    simp only [Spec_to_equiv_of_field_apply_fst, ← Scheme.comp_val_base_apply, e] },
  { simp only [Spec_to_equiv_of_field_apply_snd],
    apply radicial.residue_radicial f,
    convert_to f.map_residue_field _ ≫ _ = f.map_residue_field _ ≫ _, 
    rw [← cancel_epi (Y.to_residue_field _)], swap, { apply_instance },
    simp only [Top.presheaf.stalk_congr_hom, stalk_closed_point_to,
      Scheme.to_residue_field_of_eq_assoc, Scheme.to_residue_field_map_residue_field_assoc,
      Scheme.to_desc_residue_field,
      ← PresheafedSpace.stalk_map.stalk_specializes_stalk_map_assoc],
    slice_lhs 1 2 { rw [← PresheafedSpace.stalk_map.comp] },
    erw PresheafedSpace.stalk_map.congr_hom' _ _
      (show g₁.1 ≫ f.1 = g₂.1 ≫ f.1, by injection e),
    slice_rhs 2 3 { erw ← PresheafedSpace.stalk_map.comp },
    simp_rw category.assoc, refl }
end

lemma _root_.field.exists_common_extension {K L M : Type u} [field K] [field L] [field M]
  (f : K →+* L) (g : K →+* M) :
  ∃ (N : Type u) [field N], by exactI ∃ (h : L →+* N) (k : M →+* N), h.comp f = k.comp g :=
begin
  letI := f.to_algebra,
  letI := g.to_algebra,
  obtain ⟨m, hm⟩ := ideal.exists_maximal (tensor_product K L M),
  rw ideal.quotient.maximal_ideal_iff_is_field_quotient at hm,
  refine ⟨tensor_product K L M ⧸ m, hm.to_field,
    m^.quotient.mk^.comp algebra.tensor_product.include_left.to_ring_hom,
    m^.quotient.mk^.comp algebra.tensor_product.include_right.to_ring_hom, _⟩,
  rw [ring_hom.comp_assoc, ring_hom.comp_assoc],
  congr' 1,
  exact algebra.tensor_product.include_right.comp_algebra_map.symm,
end

lemma universally_injective_of_epi_of_field
  (H : ∀ {K : Type u} [field K],
    by exactI function.injective (λ (g : Scheme.Spec.obj (op (CommRing.of K)) ⟶ X), g ≫ f)) :
  morphism_property.universally (λ X Y (f : Scheme.hom X Y), function.injective f.1.base) f :=
begin
  intros X' Y' i₁ i₂ f' h x₁ x₂ e,
  obtain ⟨K, hK, g₁, g₂, e'⟩ := field.exists_common_extension 
    (Y'.residue_field_of_eq e ≫ f'.map_residue_field x₁ : _) (f'.map_residue_field x₂), 
  resetI,
  change X'.residue_field x₁ ⟶ CommRing.of K at g₁,
  change X'.residue_field x₂ ⟶ CommRing.of K at g₂,
  replace e' : (Y'.residue_field_of_eq e ≫ f'.map_residue_field x₁) ≫ g₁ =
    f'.map_residue_field x₂ ≫ g₂ := by convert e',
  suffices : (Spec_to_equiv_of_field K X').symm ⟨x₁, g₁⟩ =
    (Spec_to_equiv_of_field K X').symm ⟨x₂, g₂⟩,
  { injection (Spec_to_equiv_of_field K X').symm.injective this },
  have : (Spec_to_equiv_of_field K X').symm ⟨x₁, g₁⟩ ≫ f' =
    (Spec_to_equiv_of_field K X').symm ⟨x₂, g₂⟩ ≫ f',
  { dsimp only [Spec_to_equiv_of_field_symm_apply, is_pullback.cone_fst],
    simp_rw [category.assoc, ← Scheme.hom.map_residue_field_from_Spec_residue_field f',
      ← functor.map_comp_assoc, ← op_comp, ← e', op_comp, functor.map_comp_assoc,
      Scheme.residue_field_of_eq_from_Spec] },
  apply pullback_cone.is_limit.hom_ext h.is_limit,
  { exact this },
  { apply H, simp only [category.assoc, is_pullback.cone_snd, ← h.w, reassoc_of this], } 
end

lemma _root_.category_theory.is_iso_of_comp_mono {C} [category C] {X Y Z : C} 
  (f : X ⟶ Y) (g : Y ⟶ Z) [is_iso (f ≫ g)] [mono g] : is_iso f :=
begin
  haveI : is_split_epi g := ⟨⟨⟨inv (f ≫ g) ≫ f, by simp⟩⟩⟩,
  haveI : is_iso g := is_iso_of_mono_of_is_split_epi g,
  rw (show f = (f ≫ g) ≫ inv g, by simp),
  apply_instance
end

lemma Spec_to_eq_of_injective {K : Type*} [field K] {X : Scheme}
  {f₁ f₂ : Scheme.Spec.obj (op $ CommRing.of K) ⟶ X}
  {g} (hf₁ : f₁ ≫ g = 𝟙 _) (hf₂ : f₂ ≫ g = 𝟙 _) (hg : function.injective g.1.base) : f₁ = f₂ :=
begin
  haveI : subsingleton X.carrier := @@function.injective.subsingleton _ hg
    (show subsingleton (prime_spectrum K), by apply_instance),
  apply (Spec_to_equiv_of_field _ _).injective,
  refine Spec_to_equiv_of_field_eq_iff.mpr ⟨subsingleton.elim _ _, _⟩,
  simp only [Spec_to_equiv_of_field_apply_snd],
  haveI : is_iso (g.map_residue_field (f₁.1.base (local_ring.closed_point K))),
  { refine category_theory.is_iso_of_comp_mono _ _,
    swap, { exact f₁.map_residue_field (local_ring.closed_point K) },
    { rw [← Scheme.hom.map_residue_field_comp],
      let f := f₁ ≫ g, change is_iso (f.map_residue_field _), rw (show f = 𝟙 _, from hf₁),
      apply_instance },
    { rw concrete_category.mono_iff_injective_of_preserves_pullback,
      exact ring_hom.injective _ } },
  rw ← cancel_epi (g.map_residue_field (f₁.1.base (local_ring.closed_point K))),
  rw ← cancel_epi (Scheme.to_residue_field _ _), swap, { apply_instance },
  simp only [Top.presheaf.stalk_congr_hom, stalk_closed_point_to, 
    Scheme.to_residue_field_of_eq_assoc, Scheme.to_residue_field_map_residue_field_assoc,
    Scheme.to_desc_residue_field, ← PresheafedSpace.stalk_map.stalk_specializes_stalk_map_assoc],
  slice_lhs 1 2 { erw [← PresheafedSpace.stalk_map.comp] },
  slice_rhs 2 3 { erw [← PresheafedSpace.stalk_map.comp] },
  erw PresheafedSpace.stalk_map.congr_hom' _ _
    (show f₁.1 ≫ g.1 = f₂.1 ≫ g.1, by injection hf₁.trans hf₂.symm),
  simp only [category.assoc],
  refl,
end

def morphism_property.injective : morphism_property Scheme :=
λ X Y f, function.injective f.1.base 

lemma radicial_tfae :
  tfae [radicial f,
    ∀ {K : Type*} [field K], by exactI function.injective
      (λ g : Scheme.Spec.obj (op $ CommRing.of K) ⟶ X, g ≫ f),
    morphism_property.universally morphism_property.injective f,
    surjective (pullback.diagonal f)] :=
begin
  tfae_have : 1 → 2,
  { introsI _ K _, exact radicial.epi_of_field f },
  tfae_have : 2 → 3,
  { exact universally_injective_of_epi_of_field f },
  tfae_have : 3 → 2,
  { introsI H K hK g₁ g₂ e,
    let f' := g₁ ≫ f,
    rw [← pullback.lift_snd (𝟙 _) g₁ (category.id_comp f'),
      ← pullback.lift_snd (𝟙 _) g₂ ((category.id_comp f').trans e)],
    congr' 1,
    apply Spec_to_eq_of_injective (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _)
      (H _ _ _ (is_pullback.of_has_pullback f' f)) },
  tfae_have : 3 → 1,
  { intro H,
    refine ⟨(morphism_property.universally_le _ _ _ f H : _), _⟩,
    introsI x K _ f₁ f₂ e,
    change X.residue_field x ⟶ CommRing.of K at f₁,
    change X.residue_field x ⟶ CommRing.of K at f₂,
    replace e : f.map_residue_field x ≫ f₁ = f.map_residue_field x ≫ f₂ := by convert e,
    suffices : (Spec_to_equiv_of_field K X).symm ⟨x, f₁⟩ =
      (Spec_to_equiv_of_field K X).symm ⟨x, f₂⟩,
    { injection (Spec_to_equiv_of_field K X).symm.injective this, exact eq_of_heq ‹_› },
    apply tfae_3_to_2 H,
    dsimp only [Spec_to_equiv_of_field_symm_apply],
    simp only [category.assoc, ← Scheme.hom.map_residue_field_from_Spec_residue_field,
      ← functor.map_comp_assoc, ← op_comp, e] },
  tfae_have : 3 → 4,
  { rw surjective_iff,
    intros H x,
    refine ⟨(pullback.fst : pullback f f ⟶ _).1.base x,
      H _ _ _ (is_pullback.of_has_pullback f f) _⟩,
    simp only [← Scheme.comp_val_base_apply, category.assoc,
      pullback.diagonal_fst, category.comp_id] },
  tfae_have : 4 → 3,
  { suffices : morphism_property.diagonal @surjective ≤ morphism_property.injective.universally,
    { apply this },
    rw ← (surjective_stable_under_base_change.diagonal surjective_respects_iso).universally_eq,
    refine morphism_property.universally_mono _,
    intros X Y f h x y e,
    let T : pullback.triplet f f := ⟨x, y, _, e, rfl⟩,
    obtain ⟨z, hz, hz'⟩ := T.exists_preimage,
    obtain ⟨z', rfl⟩ := h.1 z,
    simp only [← Scheme.comp_val_base_apply,
      pullback.diagonal_fst, pullback.diagonal_snd] at hz hz',
    exact hz.symm.trans hz' },
  tfae_finish
end

lemma radicial_eq_univerally_injective :
  @radicial = morphism_property.universally morphism_property.injective :=
by { ext X Y f, exact (radicial_tfae f).out 0 2 }

lemma radicial_eq_diagonal_surjective :
  @radicial = morphism_property.diagonal @surjective :=
by { ext X Y f, exact (radicial_tfae f).out 0 3 }

end tfae

lemma radicial_respects_iso : 
  morphism_property.respects_iso @radicial :=
radicial_eq_univerally_injective.symm ▸ 
  morphism_property.injective.universally_respects_iso

lemma radicial_stable_under_composition : 
  morphism_property.stable_under_composition @radicial :=
radicial_eq_diagonal_surjective.symm ▸ 
  surjective_stable_under_composition.diagonal 
    surjective_respects_iso
    surjective_stable_under_base_change

lemma radicial_stable_under_base_change :
  morphism_property.stable_under_base_change @radicial :=
radicial_eq_univerally_injective.symm ▸ 
  morphism_property.universally_stable_under_base_change _

lemma radicial_is_local_at_target :
  property_is_local_at_target @radicial :=
radicial_eq_diagonal_surjective.symm ▸ 
  surjective_is_local_at_target.diagonal

instance radicial_of_mono [mono f] : radicial f :=
by { rw radicial_eq_diagonal_surjective, show surjective _, apply_instance }

end algebraic_geometry