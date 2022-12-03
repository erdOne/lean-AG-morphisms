import ring_theory.polynomial.basic
-- The contents of this file is not needed anymore

lemma is_unit_sub_of_is_unit_of_is_nilpotent {M : Type*} [comm_ring M] {a b : M}
  (ha : is_unit a) (hb : is_nilpotent b) : is_unit (a - b) :=
begin
  refine @is_unit_of_mul_is_unit_left _ _ _ ↑(ha.unit⁻¹) _,
  rw [sub_mul, is_unit.mul_coe_inv],
  obtain ⟨n, hn⟩ := commute.is_nilpotent_mul_left (mul_comm b ↑(ha.unit)⁻¹) hb,
  exact is_unit_of_mul_eq_one _ _ ((mul_neg_geom_sum _ n).trans $ hn.symm ▸ sub_zero 1)
end

lemma is_unit_add_of_is_unit_of_is_nilpotent {M : Type*} [comm_ring M] {a b : M}
  (ha : is_unit a) (hb : is_nilpotent b) : is_unit (a + b) :=
sub_neg_eq_add a b ▸ is_unit_sub_of_is_unit_of_is_nilpotent ha hb.neg

lemma is_nilpotent.sum {M : Type*} [comm_semiring M] {ι : Type*} (s : finset ι)
  (f : ι → M) (hf : ∀ i ∈ s, is_nilpotent (f i)) : is_nilpotent (s.sum f) :=
begin
  classical,
  induction s using finset.induction_on with a s h₁ h₂,
  { rw finset.sum_empty, exact is_nilpotent.zero },
  { rw [finset.sum_insert h₁],
    exact commute.is_nilpotent_add (mul_comm _ _) (hf a (finset.mem_insert_self _ _))
      (h₂ $ λ i hi, hf _ (finset.mem_insert_of_mem hi)) }
end

open_locale polynomial

lemma polynomial.is_unit_iff' {R : Type*} [comm_ring R] {p : R[X]} : 
  is_unit p ↔ is_unit (p.coeff 0) ∧ ∀ i ≠ 0, is_nilpotent (p.coeff i) :=
begin
  split,
  { intro h,
    rw polynomial.coeff_zero_eq_eval_zero,
    refine ⟨(polynomial.eval_ring_hom (0 : R)).is_unit_map h, λ i hi, _⟩,
    change p.coeff i ∈ nilradical R,
    rw [nilradical_eq_Inf, ideal.mem_Inf],
    rintros I (hI : I.is_prime),
    have := ring_hom.is_unit_map (polynomial.map_ring_hom I^.quotient.mk) h,
    resetI,
    obtain ⟨r, h₁, h₂⟩ := polynomial.is_unit_iff.mp this,
    apply_fun (λ x, polynomial.coeff x i) at h₂,
    rwa [polynomial.coeff_C_ne_zero hi, polynomial.coe_map_ring_hom, polynomial.coeff_map,
      ← ideal.quotient.mk_eq_mk, eq_comm, submodule.quotient.mk_eq_zero] at h₂ },
  { rintro ⟨h₁, h₂⟩, 
    casesI subsingleton_or_nontrivial R, { exact is_unit_of_subsingleton _ }, 
    have : 0 ∈ p.support,
    { rw [polynomial.mem_support_iff], intro e, rw e at h₁, exact not_is_unit_zero h₁ },
    rw [← p.sum_monomial_eq, polynomial.sum, ← finset.sum_filter_add_sum_filter_not _ (eq 0),
      finset.filter_eq p.support 0, if_pos this, finset.sum_singleton,
      polynomial.monomial_zero_left],
    apply is_unit_add_of_is_unit_of_is_nilpotent (polynomial.C.is_unit_map h₁),
    apply is_nilpotent.sum,
    intros i hi, rw [← mul_one (p.coeff i), ← polynomial.C_mul_monomial],
    exact commute.is_nilpotent_mul_left (mul_comm _ _)
      ((h₂ i $ ne_comm.mp (finset.mem_filter.mp hi).2).map polynomial.C) }
end
