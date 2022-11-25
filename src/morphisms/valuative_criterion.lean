import morphisms.universally_closed
import ring_theory.valuation.valuation_ring
import for_mathlib.valuation_subring
import morphisms.separated
import algebraic_geometry.properties

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universes v u

namespace algebraic_geometry

variables {X Y : Scheme.{u}} (f : X ⟶ Y)

open category_theory.morphism_property
open algebraic_geometry.morphism_property (topologically)

structure valuative_comm_sq {X Y : Scheme.{u}} (f : X ⟶ Y) :=
(R : Type.{u})
[hR : comm_ring R]
[hR₁ : is_domain R]
[hR₂ : valuation_ring R]
(K : Type.{u})
[hK : field K]
[hRK : algebra R K]
[hRK' : is_fraction_ring R K]
(i₁ : Scheme.Spec.obj (op $ CommRing.of K) ⟶ X)
(i₂ : Scheme.Spec.obj (op $ CommRing.of R) ⟶ Y)
(comm_sq : comm_sq i₁ (Scheme.Spec.map (CommRing.of_hom $ algebra_map R K).op) f i₂)
.
def valuative_criterion.existence : morphism_property Scheme :=
λ X Y f, ∀ S : valuative_comm_sq f, S.comm_sq.has_lift

def valuative_criterion.uniqueness : morphism_property Scheme :=
λ X Y f, ∀ S : valuative_comm_sq f, subsingleton S.comm_sq.lift_struct

def valuative_criterion : morphism_property Scheme :=
λ X Y f, ∀ S : valuative_comm_sq f, nonempty (unique (S.comm_sq.lift_struct))

section existence

lemma valuative_criterion.existence.specializing_map (H : valuative_criterion.existence f) :
  specializing_map f.1.base :=
begin
  rintros x y (h : f.1.base x ⤳ y),
  let ϕ := Y.presheaf.stalk_specializes h ≫ PresheafedSpace.stalk_map f.1 x ≫ X.stalk_residue x,
  obtain ⟨A, hA, hA'⟩ := exists_factor_valuation_ring ϕ,
  let ϕ' := ϕ.cod_restrict A.to_subring hA,
  have : CommRing.of_hom ϕ' ≫ CommRing.of_hom (algebra_map ↥A ↥(X.residue_field x)) = ϕ,
  { ext, refl },
  obtain ⟨⟨H'⟩⟩ := H ⟨A, X.residue_field x, X.from_Spec_residue_field x,
    Scheme.Spec.map (CommRing.of_hom ϕ').op ≫ Y.from_Spec_stalk y, ⟨_⟩⟩,
  refine ⟨H'.l.1.base (local_ring.closed_point A), _, _⟩,
  { simp only [← functor.map_comp_assoc, ← op_comp, this, ϕ],
    erw op_comp,
    simp only [op_comp, functor.map_comp_assoc],
    erw Scheme.stalk_specializes_from_Spec_stalk h,
    rw [stalk_map_from_Spec_stalk, ← category.assoc], refl },
  { show local_ring A, by apply_instance },
  { change _ ⤳ _,
    conv_lhs { rw [← Scheme.from_Spec_residue_field_base x (⊥ : prime_spectrum $ X.residue_field x),
      ← (show _ = X.from_Spec_residue_field x, from H'.fac_left)] },
    refine specializes.map _ H'.l.1.base.2,
    apply_with local_ring.specializes_closed_point { instances := ff } },
  { rw [← Scheme.comp_val_base_apply, H'.fac_right],
    dsimp only,
    erw Scheme.comp_val_base_apply,
    convert Scheme.from_Spec_stalk_closed_point _,
    apply_with local_ring.comap_closed_point { instances := ff },
    exact hA' }
end

-- move me
lemma _root_.category_theory.functor.preimage_injective {C D} [category C] [category D]
  (F : C ⥤ D) [full F] {X Y : C} : 
  function.injective (F.preimage : _ → (X ⟶ Y)) :=
λ f g e, by rw [← F.image_preimage f, ← F.image_preimage g, e]

lemma valuative_criterion.existence.of_specializing_map
  (H : universally (topologically @specializing_map) f) :
  valuative_criterion.existence f :=
begin
  rintros ⟨R, K, i₁, i₂, c⟩,
  resetI,
  let X' := pullback f i₂,
  let S := Scheme.Spec.obj (op $ CommRing.of R),
  let f' : X' ⟶ S := pullback.snd,
  let i₁' : _ ⟶ X' := pullback.lift i₁ _ c.1,
  let x' : X'.carrier := i₁'.1.base (show prime_spectrum K, from local_ring.closed_point _),
  let s' : S.carrier := (show prime_spectrum R, from local_ring.closed_point _),
  have hxs : f'.1.base x' ⤳ s' := local_ring.specializes_closed_point _,
  have hf' : specializing_map f'.1.base := H _ _ _ (is_pullback.of_has_pullback _ _).flip,
  obtain ⟨x, hx : _ ⤳ _, e⟩ := hf' hxs,
  let ϕ : CommRing.of R ⟶ X'.stalk x := structure_sheaf.to_stalk R s' ≫
    S.presheaf.stalk_specializes (specializes_of_eq e) ≫ PresheafedSpace.stalk_map f'.1 x,
  haveI : is_local_ring_hom ϕ := by apply is_local_ring_hom_comp,
  let ψ : X'.presheaf.stalk x ⟶ CommRing.of K :=
    X'.presheaf.stalk_specializes hx ≫ stalk_closed_point_to _ i₁',
  have hϕ : ϕ ≫ ψ = CommRing.of_hom (algebra_map R K),
  { simp only [ϕ, stalk_closed_point_to, category.assoc,
      ← PresheafedSpace.stalk_map.stalk_specializes_stalk_map_assoc,
      Top.presheaf.stalk_specializes_comp_assoc],
    slice_lhs 3 4 { erw ← PresheafedSpace.stalk_map.comp },
    have : i₁'.val ≫ f'.val = (Scheme.Spec.map (CommRing.of_hom (algebra_map R K)).op).1 := 
      congr_arg LocallyRingedSpace.hom.val (pullback.lift_snd i₁ _ c.1),
    erw [PresheafedSpace.stalk_map.congr_hom' _ _ this],
    simp only [category.assoc, Top.presheaf.stalk_specializes_comp_assoc],
    erw structure_sheaf.to_stalk_stalk_specializes_assoc,
    slice_lhs 1 2 { erw stalk_map_to_stalk },
    rw iso.comp_inv_eq,
    simp_rw category.assoc,
    erw structure_sheaf.to_stalk_comp_stalk_to_fiber_ring_hom,
    refl },
  have hψ := @bijective_range_restrict_comp_of_valuation_ring R (X'.presheaf.stalk x) K
    _ _ _ _ _ _ _ _ _ _ hϕ _,
  let ψ' : _ ⟶ CommRing.of R :=
    (ring_equiv.of_bijective _ hψ).symm.to_ring_hom.comp ψ.range_restrict,
  haveI : is_local_ring_hom ψ',
  { apply_with is_local_ring_hom_comp { instances := ff },
    { exact is_local_ring_hom_equiv (ring_equiv.of_bijective _ hψ).symm },
    { exact is_local_ring_hom_of_surjective _ ψ.range_restrict_surjective } },
  have hψ'' : ϕ ≫ ψ' = 𝟙 _, 
  { ext1 y, exact (ring_equiv.of_bijective _ hψ).symm_apply_apply y },
  haveI : mono (CommRing.of_hom (algebra_map R K)),
  { apply functor.mono_of_mono_map (forget CommRing), rw mono_iff_injective,
    exact (is_fraction_ring.injective R K : _) },
  have hψ' : ψ' ≫ CommRing.of_hom (algebra_map R K) = ψ, 
  { rw ← hϕ, ext1 y,
    change ((ring_equiv.of_bijective _ hψ) $ (ring_equiv.of_bijective _ hψ).symm _).1 = _,
    rw ring_equiv.apply_symm_apply, refl },
  haveI : local_ring (CommRing.of R) := show local_ring R, by apply_instance,
  refine ⟨⟨⟨(Spec_to_equiv_of_local_ring (CommRing.of R) _).symm ⟨_, ψ', infer_instance⟩
    ≫ pullback.fst, _, _⟩⟩⟩,
  { dsimp only,
    transitivity i₁' ≫ pullback.fst, swap, { exact pullback.lift_fst _ _ _ },
    rw ← category.assoc, congr' 1,
    refine (functor.map_comp_assoc _ _ _ _).symm.trans _,
    dsimp only,
    rw [← op_comp, hψ', op_comp, functor.map_comp_assoc, Scheme.stalk_specializes_from_Spec_stalk],
    exact Spec_map_stalk_closed_point_to_from_stalk _ _ },
  { dsimp only,
    rw [category.assoc, pullback.condition, ← category.assoc],
    convert category.id_comp _,
    show (_ ≫ _) ≫ f' = 𝟙 _,
    apply Scheme.Spec.preimage_injective,
    rw ← cancel_epi (CommRing.of_hom (algebra_map R K)).op,
    apply Scheme.Spec.map_injective,
    simp only [functor.map_comp, op_comp, functor.image_preimage, category.assoc],
    rw [← functor.map_comp_assoc, ← op_comp, hψ', op_comp, functor.map_comp_assoc,
      Scheme.stalk_specializes_from_Spec_stalk_assoc],
    erw Spec_map_stalk_closed_point_to_from_stalk_assoc,
    rw [pullback.lift_snd, category.comp_id] }
end
.
lemma valuative_criterion.existence_stable_under_base_change : 
  valuative_criterion.existence.stable_under_base_change :=
begin
  rintros X Y Y' S f g h k H hg ⟨R, K, i₄, i₂, c⟩,
  resetI,
  obtain ⟨⟨⟨l, hl₁, hl₂⟩⟩⟩ := hg ⟨R, K, i₄ ≫ h, i₂ ≫ f, ⟨_⟩⟩,
  obtain ⟨l', hl₃, hl₄⟩ := pullback_cone.is_limit.lift' H.is_limit l i₂ hl₂,
  refine ⟨⟨⟨l', _, hl₄⟩⟩⟩,
  apply pullback_cone.is_limit.hom_ext H.is_limit,
  { simp only [category.assoc, hl₃, hl₁], refl },
  { simp only [category.assoc, hl₄, c.w.symm], refl },
  { simp only [category.assoc, ← c.w_assoc, H.w] }
end

lemma valuative_criterion.existence_eq :
  valuative_criterion.existence = universally (topologically @specializing_map) :=
begin
  apply le_antisymm,
  { rw ← valuative_criterion.existence_stable_under_base_change.universally_eq,
    exact universally_mono (λ X Y f, valuative_criterion.existence.specializing_map f) },
  { exact λ X Y f, valuative_criterion.existence.of_specializing_map f }
end

lemma universally_closed_eq_valuative_criterion : 
  @universally_closed = @quasi_compact ⊓ valuative_criterion.existence :=
by rw [valuative_criterion.existence_eq,
  universally_closed_eq_quasi_compact_and_universally_specializing]

lemma universally_closed_of_valuative_criterion [quasi_compact f]
  (hf : valuative_criterion.existence f) : universally_closed f :=
begin
  rw universally_closed_eq_valuative_criterion,
  exact ⟨infer_instance, hf⟩
end


end existence

section uniqueness

lemma separated_of_valuative_criterion [quasi_separated f]
  (hf : valuative_criterion.uniqueness f) : separated f :=
begin
  suffices : universally_closed (pullback.diagonal f),
  { constructor,
    apply is_closed_immersion.of_is_immersion,
    exactI (universally_closed.is_closed_map $ pullback.diagonal f).closed_range },
  apply universally_closed_of_valuative_criterion,
  rintro ⟨R, K, i₁, i₂, c⟩,
  resetI,
  have c' : comm_sq i₁ (Scheme.Spec.map (CommRing.of_hom (algebra_map R K)).op) f
    (i₂ ≫ pullback.fst ≫ f),
  { constructor, rw [← c.w_assoc, pullback.diagonal_fst_assoc] },
  have : i₂ ≫ pullback.fst = i₂ ≫ pullback.snd,
  { injection @@subsingleton.elim (hf ⟨R, K, i₁, i₂ ≫ pullback.fst ≫ f, c'⟩)
      ⟨i₂ ≫ pullback.fst, _, category.assoc _ _ _⟩ ⟨i₂ ≫ pullback.snd, _, _⟩; dsimp only,
    { rw [← c.w_assoc, pullback.diagonal_fst, category.comp_id] },
    { rw [← c.w_assoc, pullback.diagonal_snd, category.comp_id] },
    { rw [category.assoc, pullback.condition] } },
  refine ⟨⟨⟨i₂ ≫ pullback.fst, _, _⟩⟩⟩; dsimp only,
  { rw [← c.w_assoc, pullback.diagonal_fst, category.comp_id] },
  { apply pullback.hom_ext; simp only [category.assoc, pullback.diagonal_fst, pullback.diagonal_snd,
      category.comp_id, this] }
end
.

--move me
def Spec_Γ_arrow_iso_of_is_affine [is_affine X] [is_affine Y] :
  arrow.mk f ≅ arrow.mk (Scheme.Spec.map (Scheme.Γ.map f.op).op) :=
arrow.iso_mk' _ _ (as_iso $ Γ_Spec.adjunction.unit.app _) (as_iso $ Γ_Spec.adjunction.unit.app _)
  (Γ_Spec.adjunction.unit_naturality f)

--move me
def Γ_Spec_arrow_iso {R S : CommRing} (f : R ⟶ S) :
  arrow.mk f ≅ arrow.mk (Scheme.Γ.map (Scheme.Spec.map f.op).op) :=
(arrow.iso_of_nat_iso Spec_Γ_identity (arrow.mk f)).symm

lemma separated.valuative_criterion [separated f] :
  valuative_criterion.uniqueness f :=
begin
  rintro ⟨R, K, i₁, i₂, c⟩,
  constructor,
  rintro ⟨l₁, hl₁, hl₁'⟩ ⟨l₂, hl₂, hl₂'⟩,
  ext1,
  dsimp only at *,
  let h := hl₁'.trans hl₂'.symm,
  have := is_closed_immersion_stable_under_base_change
    (pullback_fst_map_snd_is_pullback f f (pullback.diagonal f)
    (pullback.lift l₁ l₂ h)) infer_instance,
  haveI : is_iso (pullback.diagonal f ≫ pullback.snd),
  { rw [pullback.diagonal_snd], apply_instance },
  rw ← is_closed_immersion_respects_iso.cancel_right_is_iso _ pullback.snd at this,
  swap, { apply_instance },
  rw [pullback.lift_snd, category.comp_id] at this,
  let Z := pullback (pullback.diagonal f) (pullback.lift l₁ l₂ h),
  let g : Z ⟶ _ := pullback.snd,
  change is_closed_immersion g at this,
  resetI,
  haveI : is_affine Z := is_affine_of_affine g,
  have hg₂ := ((is_closed_immersion_over_affine_iff g).mp this).2,
  suffices : is_iso g,
  { resetI, 
    refine (pullback.lift_fst l₁ l₂ h).symm.trans (eq.trans _ (pullback.lift_snd l₁ l₂ h)),
    rw [← cancel_epi g, ← pullback.condition_assoc, ← pullback.condition_assoc,
      pullback.diagonal_fst, pullback.diagonal_snd] },
  let l : Scheme.Spec.obj (op $ CommRing.of K) ⟶ Z :=
    pullback.lift i₁ (Scheme.Spec.map (CommRing.of_hom (algebra_map R K)).op) _,
  swap,
  { apply pullback.hom_ext; simp only [pullback.diagonal_fst, pullback.diagonal_snd,
      category.assoc, category.comp_id, pullback.lift_fst, pullback.lift_snd, hl₁, hl₂] },
  have hg : l ≫ g = Scheme.Spec.map (CommRing.of_hom (algebra_map R K)).op := pullback.lift_snd _ _ _,
  have hg₁ := ((morphism_property.injective_respects_iso _).arrow_mk_iso_iff
    (Γ_Spec_arrow_iso $ CommRing.of_hom $ algebra_map R K)).mp (is_fraction_ring.injective R K : _),
  rw [← hg, op_comp, functor.map_comp] at hg₁,
  rw is_iso_respects_iso.arrow_mk_iso_iff (Spec_Γ_arrow_iso_of_is_affine g),
  convert_to is_iso
    (Scheme.Spec.map (ring_equiv.of_bijective _ ⟨hg₁.of_comp, hg₂⟩).to_CommRing_iso.hom.op),
  apply_instance
end

lemma separated_eq_valuative_criterion :
  @separated = @quasi_separated ⊓ valuative_criterion.uniqueness :=
begin
  ext X Y f, split,
  { introI H, exact ⟨infer_instance, separated.valuative_criterion f⟩ },
  { rintro ⟨h₁, h₂⟩, exactI separated_of_valuative_criterion f h₂ }
end

end uniqueness

end algebraic_geometry