import ring_theory.local_properties
.

open polynomial

lemma ring_hom.localization_is_integral :
  ring_hom.localization_preserves (λ R S _ _ f, by exactI f.is_integral) :=
begin
  introsI R S _ _ f M R' S' _ _ _ _ _ _ hf,
  letI := f.to_algebra,
  exact is_integral_localization (show algebra.is_integral R S, from hf)
end

lemma ring_hom.is_integral_of_localization_span :
  ring_hom.of_localization_span (λ R S _ _ f, by exactI f.is_integral) :=
begin
  introsI R S _ _ f s hs H x,
  letI := f.to_algebra,
  apply (integral_closure R S).to_submodule.mem_of_span_eq_top_of_smul_pow_mem _ hs,
  intros r,
  letI := (localization.away_map f r).to_algebra,
  haveI : is_scalar_tower R (localization.away (r : R)) (localization.away $ f r) := 
    is_scalar_tower.of_algebra_map_eq' (is_localization.map_comp _).symm,
  haveI : is_scalar_tower R S (localization.away $ f r) := 
    is_scalar_tower.of_algebra_map_eq' rfl,
  obtain ⟨⟨_, n, rfl⟩, p, hp, hp'⟩ := is_integral.exists_multiple_integral_of_is_localization
    (submonoid.powers (r : R)) _ (H r (algebra_map _ _ x)),
  simp only [submonoid.smul_def, subtype.coe_mk, algebra.smul_def, ring_hom.comp_apply,
    is_scalar_tower.algebra_map_eq R S (localization.away $ f r), ← map_mul] at hp',
  rw [eval₂_eq_eval_map, ← map_map, eval_map, eval₂_at_apply, ← @is_localization.mk'_one _ _
    (submonoid.powers $ f r), is_localization.mk'_eq_zero_iff] at hp',
  obtain ⟨⟨_, m, rfl⟩, H'⟩ := hp',
  rw [subtype.coe_mk, mul_comm, ← map_pow, ← ring_hom.algebra_map_to_algebra f,
    eval_map, ← eval₂_smul] at H',
  by_cases (r : R) ^ m = 0, { use m, rw [h, zero_smul], exact zero_mem _ },
  have hp'' : ((r : R) ^ m • p).leading_coeff = (r : R) ^ m,
  { have hp'' : ((r : R) ^ m • p).coeff p.nat_degree = (r : R) ^ m,
    { rw [coeff_smul, coeff_nat_degree, hp.leading_coeff, smul_eq_mul, mul_one] },
    have : ((r : R) ^ m • p).nat_degree = p.nat_degree,
    { exact (nat_degree_smul_le _ _).antisymm (le_nat_degree_of_ne_zero $ hp''.trans_ne h) },
    rw [leading_coeff, this, hp''] },
  have := is_integral_leading_coeff_smul _ _ H',
  rw [hp'', ← algebra.smul_def, smul_smul, ← pow_add] at this,
  exact ⟨m+n, this⟩
end
