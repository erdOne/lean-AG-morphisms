import logic.equiv.transfer_instance
import ring_theory.valuation.valuation_subring


variables {K: Type*} [field K] (A : valuation_subring K)

open local_ring

def local_subring (K : Type*) [comm_ring K] : Type* :=
{ s : subring K // local_ring s }

instance : partial_order (local_subring K) :=
{ le := λ A B, ∃ h : A.1 ≤ B.1, is_local_ring_hom (subring.inclusion h),
  le_refl := λ A, ⟨rfl.le, ⟨λ a ha, by { cases a, exact ha }⟩⟩,
  le_trans := λ A B C ⟨hAB, hAB'⟩ ⟨hBC, hBC'⟩,
    ⟨hAB.trans hBC, @@is_local_ring_hom_comp _ _ _ _ _ hBC' hAB'⟩,
  le_antisymm := λ A B ⟨hAB, hAB'⟩ ⟨hBA, hBA'⟩, subtype.ext (hAB.antisymm hBA) }

def valuation_subring.to_local_subring (A : valuation_subring K) : local_subring K :=
⟨A.to_subring, show local_ring A, by apply_instance⟩ 

lemma valuation_subring.to_local_subring_injective : 
  function.injective (valuation_subring.to_local_subring : _ → local_subring K) :=
λ A B e, by { ext, change x ∈ A.to_local_subring.1 ↔ _, rw e, refl }

lemma subring.is_unit_iff {K : Type*} [division_ring K] {A : subring K} (x : A) (hx : x ≠ 0) :
  is_unit x ↔ (x : K)⁻¹ ∈ A :=
begin
  split,
  { rintro ⟨⟨x, y, hxy, hyx⟩, rfl⟩,
    convert y.2,
    rw inv_eq_of_mul_eq_one_left,
    exact subtype.ext_iff.mp hyx },
  { intro h, 
    have : (x : K) ≠ 0 := by { contrapose! hx, ext1, exact hx },
    refine ⟨⟨x, ⟨_, h⟩, _, _⟩, rfl⟩; ext; simp [inv_mul_cancel this, mul_inv_cancel this] }
end

lemma local_subring.range_valuation_subring : 
  set.range valuation_subring.to_local_subring = maximals (≤) (set.univ : set $ local_subring K) :=
sorry
-- begin
--   ext A, split,
--   sorry; { rintro ⟨A, rfl⟩,
--     refine ⟨trivial, _⟩,
--     rintro B - ⟨hB, hB'⟩,
--     apply eq.le,
--     refine subtype.ext (hB.antisymm _).symm,
--     intros x hx,
--     cases A.2 x, { assumption },
--     by_cases hx : x⁻¹ = 0, { rw inv_eq_zero.mp hx, exact zero_mem _ },
--     have := hB'.1 ⟨_, h⟩,
--     rw [subring.is_unit_iff, subring.is_unit_iff, subtype.coe_mk, inv_inv] at this,
--     { apply this, show x⁻¹⁻¹ ∈ B.1, rwa inv_inv },
--     { contrapose! hx, injection hx },
--     { contrapose! hx, injection hx } },
--   { rintros ⟨-, hA⟩, refine ⟨⟨A.1, λ x, or_iff_not_imp_left.mpr $ λ hx, _⟩, subtype.ext rfl⟩,
--     let A' := subring.closure (↑A.1 ∪ {x} : set K),
--     have hA' : A.1 ≤ A' := by { intros x hx, apply subring.subset_closure, exact or.inl hx },
--     have hx' : x ∈ A' := subring.subset_closure (or.inr rfl),
--     haveI := A.2,
--     have : (local_ring.maximal_ideal A.1).map (subring.inclusion hA') = ⊤,
--     sorry; { refine (not_not.mp $ λ h, _),
--       obtain ⟨m, hm, hm'⟩ := ideal.exists_le_maximal _ h,
--       haveI hm'' : m.comap (subring.inclusion hA') = local_ring.maximal_ideal _,
--       { symmetry, apply (local_ring.maximal_ideal.is_maximal _).eq_of_le,
--         { introI e, exact (ideal.is_prime.comap (subring.inclusion hA')).1 e },
--         { rwa ← ideal.map_le_iff_le_comap } },
--       let f := @is_localization.lift _ _ m.prime_compl (localization.at_prime m) _ _ _ _ _
--         (subring.subtype A') (λ ⟨y, hy⟩, is_unit_iff_ne_zero.mpr $ λ e, hy $ by
--         { obtain rfl : y = 0 := subtype.ext (e.trans A'.subtype.map_zero.symm), exact m.zero_mem }),
--       have hf : function.injective f,
--       { rw injective_iff_map_eq_zero, intros x hx,
--         obtain ⟨x, s, rfl⟩ := is_localization.mk'_surjective m.prime_compl x,
--         rw [is_localization.lift_mk', eq_comm, units.eq_mul_inv_iff_mul_eq, zero_mul] at hx,
--         obtain rfl : x = 0 := subtype.ext (hx.symm.trans A'.subtype.map_zero.symm),
--         rw is_localization.mk'_zero },
--       let f' := ring_equiv.of_left_inverse hf.has_left_inverse.some_spec,
--       have : A' ≤ f.range,
--       { intros x hx, refine ⟨is_localization.mk' _ (⟨x, hx⟩ : A') (1 : m.prime_compl), _⟩,
--         rw [is_localization.lift_mk', map_one, inv_one, units.coe_one, mul_one], refl },
--       refine hx ((@hA ⟨f.range, _⟩ trivial ⟨hA'.trans this, _⟩).some (this hx')),
--       { exact f'.local_ring },
--       { constructor, rintros y hy, 
--         have : subring.inclusion (hA'.trans this) y =
--           f' (algebra_map _ _ (subring.inclusion hA' y)),
--         { ext1, change _ = f _, rw is_localization.lift_eq, refl },
--         rw [this, ← ring_equiv.coe_to_ring_hom, is_unit_map_iff ↑f',
--           is_localization.at_prime.is_unit_to_map_iff _ m] at hy, 
--         apply not_not.mp,
--         change y ∉ local_ring.maximal_ideal A.1,
--         rw ← hm'',
--         exact hy,
--         all_goals { apply_instance } } }, 
--     -- { by_contra h, }
--      }
-- end

lemma exists_valuation_subring_dominates (A : local_subring K) :
  ∃ (B : valuation_subring K), A ≤ B.to_local_subring := sorry


lemma is_local_ring_hom_of_surjective {R S : Type*} [comm_ring R] [local_ring R] [comm_ring S]
  [nontrivial S]
  (f : R →+* S) (hf : function.surjective f) : is_local_ring_hom f :=
begin
  haveI := local_ring.of_surjective' _ hf,
  have := ideal.comap_map_of_surjective f hf (local_ring.maximal_ideal R),
  rw [sup_eq_left.mpr _] at this,
  rw [(local_hom_tfae f).out 0 3, ← this],
  { refine ideal.comap_mono (le_maximal_ideal _),
    intro e, rw e at this, exact (maximal_ideal.is_maximal R).ne_top this.symm },
  { apply le_maximal_ideal, intro e, apply @one_ne_zero S, rw ← f.map_one,
    change (1 : R) ∈ ideal.comap f ⊥, rw e, trivial }
end

lemma bijective_range_restrict_comp_of_valuation_ring {R S K : Type*} [comm_ring R] 
  [is_domain R] [valuation_ring R] 
  [comm_ring S] [local_ring S] [field K] [algebra R K] [is_fraction_ring R K]
  (f : R →+* S) (g : S →+* K) (h : g.comp f = algebra_map R K) [is_local_ring_hom f] : 
  function.bijective (g.range_restrict.comp f) :=
begin
  haveI := local_ring.of_surjective' _ g.range_restrict_surjective,
  haveI H := local_ring.of_surjective' _ (algebra_map R K).range_restrict_surjective,
  have : (⟨(algebra_map R K).range, H⟩ : local_subring K) ∈
    maximals (≤) (set.univ : set $ local_subring K),
  { rw ← @local_subring.range_valuation_subring K,
    exact ⟨⟨_, λ x, valuation_ring.is_integer_or_is_integer R x⟩, subtype.ext rfl⟩ },
  refine ⟨λ x y e, is_fraction_ring.injective R K _, _⟩,
  { rw ← h, exact (congr_arg subtype.val e : _) },
  suffices : (show local_subring K, from ⟨g.range, infer_instance⟩) ≤ ⟨(algebra_map R K).range, H⟩,
  { intro x, obtain ⟨y, e⟩ := this.some x.prop, use y, rw ← h at e, ext1, exact e },
  refine this.2 trivial ⟨_, _⟩,
  { rintro _ ⟨x, rfl⟩, rw ← h, exact ⟨_, rfl⟩ },
  { generalize_proofs h',
    let e := ring_equiv.of_left_inverse (is_fraction_ring.injective R K).has_left_inverse.some_spec,
    have : (subring.inclusion h') = (g.range_restrict.comp f).comp e.symm.to_ring_hom,
    { ext x, obtain ⟨x, rfl⟩ := e.surjective x, change _ = (g.comp f) (e.symm _),
      rw [h, e.symm_apply_apply], refl },
    rw this,
    apply_with is_local_ring_hom_comp { instances := ff },
    apply_with is_local_ring_hom_comp { instances := ff },
    { exact is_local_ring_hom_of_surjective _ g.range_restrict_surjective },
    { assumption },
    { exact is_local_ring_hom_equiv e.symm } },
end

lemma exists_factor_valuation_ring {R : Type*} [comm_ring R] [local_ring R] {K : Type*} [field K] 
  (f : R →+* K) :
    ∃ (A : valuation_subring K) h, is_local_ring_hom (f.cod_restrict A.to_subring h) :=
begin
  obtain ⟨B, hB, hB'⟩ := exists_valuation_subring_dominates ⟨f.range,
    local_ring.of_surjective' _ f.range_restrict_surjective⟩,
  haveI := is_local_ring_hom_of_surjective _ f.range_restrict_surjective,
  exact ⟨B, λ x, hB ⟨x, rfl⟩, is_local_ring_hom_comp (subring.inclusion hB) f.range_restrict⟩
end