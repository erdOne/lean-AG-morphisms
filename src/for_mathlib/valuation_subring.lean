import logic.equiv.transfer_instance
import ring_theory.valuation.valuation_subring
import algebraic_geometry.prime_spectrum_more
import for_mathlib.local_ring
import for_mathlib.ideal


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

instance : has_coe_to_sort (local_subring K) Type* := ⟨λ s, s.1⟩
instance local_subring.local_ring (A : local_subring K) : local_ring A := A.2

def valuation_subring.to_local_subring (A : valuation_subring K) : local_subring K :=
⟨A.to_subring, show local_ring A, by apply_instance⟩ 

lemma valuation_subring.to_local_subring_injective : 
  function.injective (valuation_subring.to_local_subring : _ → local_subring K) :=
λ A B e, by { ext, change x ∈ A.to_local_subring.1 ↔ _, rw e, refl }

def maximal_local_subrings (K : Type*) [field K] : set (local_subring K) :=
maximals (≤) (set.univ : set $ local_subring K)

open_locale polynomial

lemma maximal_ideal_map_eq_top_of_mem_maximal_local_subrings {R : local_subring K}
  (hR : R ∈ maximal_local_subrings K) {S : subring K} (hS : R.1 < S) :
    (local_ring.maximal_ideal R).map (subring.inclusion hS.le) = ⊤ :=
begin
  replace hR := hR.2,
  refine (not_not.mp $ λ h, _),
  obtain ⟨m, hm, hm'⟩ := ideal.exists_le_maximal _ h,
  haveI hm'' : m.comap (subring.inclusion hS.le) = local_ring.maximal_ideal R,
  { symmetry, apply (local_ring.maximal_ideal.is_maximal _).eq_of_le,
    { introI e, exact (ideal.is_prime.comap (subring.inclusion hS.le)).1 e },
    { rwa ← ideal.map_le_iff_le_comap } },
  let f := @is_localization.lift _ _ m.prime_compl (localization.at_prime m) _ _ _ _ _
    S.subtype (λ ⟨y, hy⟩, is_unit_iff_ne_zero.mpr $ λ e, hy $ by
    { obtain rfl : y = 0 := subtype.ext (e.trans S.subtype.map_zero.symm), exact m.zero_mem }),
  have hf : function.injective f,
  { rw injective_iff_map_eq_zero, intros x hx,
    obtain ⟨x, s, rfl⟩ := is_localization.mk'_surjective m.prime_compl x,
    rw [is_localization.lift_mk', eq_comm, units.eq_mul_inv_iff_mul_eq, zero_mul] at hx,
    obtain rfl : x = 0 := subtype.ext (hx.symm.trans S.subtype.map_zero.symm),
    rw is_localization.mk'_zero },
  let f' := ring_equiv.of_left_inverse hf.has_left_inverse.some_spec,
  have : S ≤ f.range,
  { intros x hx, refine ⟨is_localization.mk' _ (⟨x, hx⟩ : S) (1 : m.prime_compl), _⟩,
    rw [is_localization.lift_mk', map_one, inv_one, units.coe_one, mul_one], refl },
  have hS' := set_like.le_def.not.mp (not_le_of_lt hS),
  push_neg at hS',
  obtain ⟨x, hx, hx'⟩ := hS',
  refine hx' ((@hR ⟨f.range, _⟩ trivial ⟨hS.le.trans this, _⟩).some (this hx)),
  { exact f'.local_ring },
  { constructor, rintros y hy, 
    have : subring.inclusion (hS.le.trans this) y =
      f' (algebra_map _ _ (subring.inclusion hS.le y)),
    { ext1, change _ = f _, rw is_localization.lift_eq, refl },
    rw [this, ← ring_equiv.coe_to_ring_hom, is_unit_map_iff ↑f',
      is_localization.at_prime.is_unit_to_map_iff _ m] at hy, 
    apply not_not.mp,
    change y ∉ local_ring.maximal_ideal R,
    rw ← hm'',
    exact hy,
    all_goals { apply_instance } }
end

lemma algebra.mem_ideal_map_adjoin {R S : Type*} [comm_ring R] [comm_ring S] [algebra R S]
  (x : S) (I : ideal R) {y : algebra.adjoin R ({x} : set S)} :
  y ∈ I.map (algebra_map R $ algebra.adjoin R ({x} : set S)) ↔
    ∃ p : R[X], (∀ i, p.coeff i ∈ I) ∧ polynomial.aeval x p = y :=
begin
  let f : R[X] →ₐ[R] algebra.adjoin R ({x} : set S) :=
    polynomial.aeval ⟨x, algebra.self_mem_adjoin_singleton R x⟩,
  have hf : f.to_ring_hom.comp polynomial.C = algebra_map _ _ := f.comp_algebra_map,
  have : ∀ p, (f p : S) = polynomial.aeval x p,
  { intro p, change _ = polynomial.aeval ((algebra_map (algebra.adjoin R ({x} : set S))) S
      ⟨x, algebra.self_mem_adjoin_singleton R x⟩) p, rw polynomial.aeval_algebra_map_apply, refl },
  rw [← hf, ideal.map_comp, ideal.mem_map_iff_of_surjective],
  simp_rw [ideal.mem_map_C_iff, subtype.ext_iff, alg_hom.to_ring_hom_eq_coe,
    alg_hom.coe_to_ring_hom, this],
  rintro ⟨y, hy⟩,
  obtain ⟨p, rfl⟩ : y ∈ (polynomial.aeval x : R[X] →ₐ[R] S).range :=
    by rwa ← algebra.adjoin_singleton_eq_range_aeval,
  exact ⟨p, subtype.ext (this _)⟩
end

instance : has_mem K (local_subring K) := ⟨λ x K, x ∈ K.1⟩

lemma mem_of_mem_maximal_local_subrings_of_is_integral {R : local_subring K}
  (hR : R ∈ maximal_local_subrings K) {x : K} (hx : is_integral R x) : x ∈ R :=
begin
  by_contra hx',
  have H : R.1 < (algebra.adjoin R {x}).to_subring,
  { rw set_like.lt_iff_le_and_exists,
    exact ⟨λ y hy, (algebra.adjoin R {x}).algebra_map_mem ⟨y, hy⟩, x,
      algebra.subset_adjoin (set.mem_singleton x), hx'⟩ },
  have h₁ := maximal_ideal_map_eq_top_of_mem_maximal_local_subrings hR H,
  have h₂ : algebra.is_integral R (algebra.adjoin R ({x} : set K)),
  { rwa [← le_integral_closure_iff_is_integral, algebra.adjoin_le_iff,
      set.singleton_subset_iff] },
  obtain ⟨p, hp⟩ := prime_spectrum.surjective_of_is_integral_of_injective _ h₂
    (λ x y e, by { ext, injection e }) (local_ring.closed_point _),
  apply p.2.ne_top,
  rw [eq_top_iff, ← h₁, ideal.map_le_iff_le_comap],
  exact le_of_eq (by injection hp.symm)
end

lemma local_subring.range_valuation_subring : 
  set.range valuation_subring.to_local_subring = maximal_local_subrings K :=
begin
  ext A, split,
  { rintro ⟨A, rfl⟩,
    refine ⟨trivial, _⟩,
    rintro B - ⟨hB, hB'⟩,
    apply eq.le,
    refine subtype.ext (hB.antisymm _).symm,
    intros x hx,
    cases A.2 x, { assumption },
    by_cases hx : x⁻¹ = 0, { rw inv_eq_zero.mp hx, exact zero_mem _ },
    have := hB'.1 ⟨_, h⟩,
    rw [subring.is_unit_iff, subring.is_unit_iff, subtype.coe_mk, inv_inv] at this,
    { apply this, show x⁻¹⁻¹ ∈ B.1, rwa inv_inv },
    { contrapose! hx, injection hx },
    { contrapose! hx, injection hx } },
  { rintros hA, refine ⟨⟨A.1, λ x, or_iff_not_imp_left.mpr $ λ hx, _⟩, subtype.ext rfl⟩,
    apply mem_of_mem_maximal_local_subrings_of_is_integral hA,
    let A' := algebra.adjoin A ({x} : set K),
    have hA' : A.1 ≤ A'.to_subring := λ x hx, A'.algebra_map_mem ⟨x, hx⟩,
    have hx' : x ∈ A' := algebra.subset_adjoin (set.mem_singleton x),
    have hx'' : x ≠ 0 := λ e, hx (e.symm ▸ A.1.zero_mem),
    have : (local_ring.maximal_ideal A).map (algebra_map A A') = ⊤,
    { refine maximal_ideal_map_eq_top_of_mem_maximal_local_subrings hA (lt_of_le_not_le hA' _),
      exact λ e, hx (e hx') }, 
    rw [ideal.eq_top_iff_one, algebra.mem_ideal_map_adjoin x (maximal_ideal A)] at this,
    obtain ⟨p, hp₁, hp₂⟩ := this,
    have hp₃ : polynomial.aeval x (p - 1) = 0,
    { rw [map_sub, polynomial.aeval_one, hp₂], exact sub_self 1 },
    haveI : invertible x := invertible_of_nonzero hx'',
    rw [polynomial.aeval_def, ← polynomial.eval₂_reverse_eq_zero_iff, inv_of_eq_inv] at hp₃,
    suffices hp₄ : is_unit (p - 1).reverse.leading_coeff,
    { have := is_integral_leading_coeff_smul _ _ hp₃,
      rw [algebra.smul_def, mul_comm] at this,
      refine is_integral_of_is_integral_mul_unit _ this,
      swap, rw [← map_mul, ← (algebra_map A K).map_one], congr' 1, exact hp₄.coe_inv_mul },
    have : (p - 1).nat_trailing_degree = 0,
    { rw ← le_zero_iff,
      apply polynomial.nat_trailing_degree_le_of_ne_zero _,
      rw [polynomial.coeff_sub, polynomial.coeff_one_zero, sub_ne_zero],
      intro e,
      apply (maximal_ideal.is_maximal A).ne_top,
      rw [ideal.eq_top_iff_one, ← e],
      apply hp₁ },
    rw [polynomial.reverse_leading_coeff, polynomial.trailing_coeff,
      this, polynomial.coeff_sub, polynomial.coeff_one_zero, ← is_unit.neg_iff, neg_sub],
    exact (local_ring.is_unit_or_is_unit_of_add_one
      $ sub_add_cancel 1 (p.coeff 0)).resolve_right (hp₁ 0) }
end

lemma exists_valuation_subring_dominates (A : local_subring K) :
  ∃ (B : valuation_subring K), A ≤ B.to_local_subring :=
begin
  let S := { B : local_subring K | A ≤ B },
  suffices : ∃ B ∈ S, A ≤ B ∧ ∀ B' ∈ S, B ≤ B' → B' = B,
  { obtain ⟨B, -, hB, hB'⟩ := this,
    obtain ⟨B, rfl⟩ : B ∈ (set.range valuation_subring.to_local_subring : set (local_subring K)),
    { rw local_subring.range_valuation_subring,
      exact ⟨trivial, λ B' _ h, (hB' B' (le_trans hB h) h).le⟩ },
    exact ⟨B, hB⟩ },
  apply zorn_nonempty_partial_order₀, swap, { exact le_refl _ },
  intros c hc hc' B hB,
  haveI : nonempty c := ⟨⟨B, hB⟩⟩,
  have hdir : directed has_le.le (λ (i : c), i.1.1),
  { apply is_chain.directed, intros i hi j hj e, apply or_of_or_of_imp_of_imp (hc' hi hj e),
    all_goals { exact λ x, x.some } },
  let X : local_subring K := ⟨⨆ i : c, i.1.1, ⟨_⟩⟩,
  swap,
  { rintros ⟨a, ha⟩ ⟨b, hb⟩ hab,
    rw subring.mem_supr_of_directed hdir at ha hb,
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := ⟨ha, hb⟩,
    obtain ⟨k, hak, hbk⟩ := hdir i j,
    have : k.1.1 ≤ ⨆ i : c, i.1.1 := le_supr (λ i : c, i.1.1) k,
    apply or_of_or_of_imp_of_imp (@@local_ring.is_unit_or_is_unit_of_add_one _ k.1.2
      (show (⟨a, hak hi⟩ + ⟨b, hbk hj⟩ : k.1.1) = 1, by { ext, injection hab })),
    all_goals { exact (subring.inclusion this).is_unit_map } },
  have : ∀ (C : c), C.1 ≤ X,
  { intro C,
    refine ⟨le_supr _ C, ⟨λ x hx, _⟩⟩,
    obtain ⟨D, hD⟩ := (subring.mem_supr_of_directed hdir).mp (hx.unit⁻¹).1.prop,
    obtain ⟨E, hCE, hDE⟩ := hc'.directed C D,
    apply hCE.some_spec.1,
    refine is_unit_of_mul_eq_one _ ⟨_, hDE.some hD⟩ _,
    ext, injection hx.mul_coe_inv },
  exact ⟨X, le_trans (hc hB) (this ⟨B, hB⟩), λ C hC, this ⟨C, hC⟩⟩
end

lemma bijective_range_restrict_comp_of_valuation_ring {R S K : Type*} [comm_ring R] 
  [is_domain R] [valuation_ring R] 
  [comm_ring S] [local_ring S] [field K] [algebra R K] [is_fraction_ring R K]
  (f : R →+* S) (g : S →+* K) (h : g.comp f = algebra_map R K) [is_local_ring_hom f] : 
  function.bijective (g.range_restrict.comp f) :=
begin
  haveI := local_ring.of_surjective' _ g.range_restrict_surjective,
  haveI H := local_ring.of_surjective' _ (algebra_map R K).range_restrict_surjective,
  have : (⟨(algebra_map R K).range, H⟩ : local_subring K) ∈ maximal_local_subrings K,
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