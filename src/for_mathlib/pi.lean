import algebraic_geometry.prime_spectrum.basic

open_locale big_operators

lemma pi.single_apply_eq_zero {ι : Type*} {R : ι → Type*} [∀ i, has_zero (R i)] [decidable_eq ι]
  {i j : ι} (h : i ≠ j) (x : R i) : pi.single i x j = 0 :=
dif_neg h.symm

lemma pi.single_mul_eq_single {ι : Type*} {R : ι → Type*} [decidable_eq ι]
  [∀ i, monoid_with_zero (R i)]
  (i : ι) (x : R i) (f) :
  pi.single i x * f = pi.single i (x * f i) :=
begin
  ext j,
  by_cases i = j,
  { subst h, simp },
  { simp [pi.single_apply_eq_zero h] },
end

lemma pi.sum_single_eq {ι : Type*} [fintype ι] {R : ι → Type*} [decidable_eq ι]
  [∀ i, add_comm_monoid (R i)] (x : Π i, R i) : ∑ i, pi.single i (x i) = x :=
by { ext i, simp [pi.single, function.update] }

lemma ideal.span_range_pi_single {ι : Type*} [finite ι] [decidable_eq ι] {R : ι → Type*}
  [∀ i, comm_ring (R i)] :
  ideal.span (set.range $ λ i : ι, pi.single i 1 : set $ Π i, R i) = ⊤ :=
begin
  rw eq_top_iff,
  rintro x -,
  haveI := fintype.of_finite ι,
  rw ← pi.sum_single_eq x,
  refine sum_mem (λ i _, _),
  rw [← mul_one (x i), pi.single_mul i (x i)],
  exact ideal.mul_mem_left _ _ (ideal.subset_span $ set.mem_range_self i),
end

lemma prime_spectrum.pi_exists_unique {ι : Type*} [finite ι] {R : ι → Type*} [∀ i, comm_ring (R i)]
  (p : prime_spectrum (Π i, R i)) : ∃! i, ∃ q, prime_spectrum.comap (pi.eval_ring_hom R i) q = p :=
begin
  haveI := fintype.of_finite ι,
  classical,
  obtain ⟨i, hi⟩ : ∃ i, (pi.single i 1 : Π i, R i) ∉ p.as_ideal,
  { by_contra h, push_neg at h, apply p.2.1,
    rw [eq_top_iff, ← ideal.span_range_pi_single, ideal.span_le], rintro _ ⟨i, rfl⟩, exact h i },
  have : ∀ j ≠ i, (pi.single j 1 : Π i, R i) ∈ p.as_ideal,
  { by_contra h, push_neg at h, obtain ⟨j, hj, hj'⟩ := h,
    have : (pi.single i 1 * pi.single j 1 : Π i, R i) = 0,
    { ext k, cases hj.ne_or_ne k; simp [pi.single_apply_eq_zero h] },
    exact hj' ((p.2.mem_or_mem_of_mul_eq_zero this).resolve_left hi) },
  refine ⟨i, _, _⟩,
  { change p ∈ set.range (prime_spectrum.comap (pi.eval_ring_hom R i)),
    rw [prime_spectrum.range_comap_of_surjective],
    { rintros x (hx : x i = 0),
      rw [set_like.mem_coe, ← pi.sum_single_eq x],
      apply sum_mem,
      rintro j -,
      by_cases hj : j = i,
      { subst hj, rw [hx, pi.single_zero], exact zero_mem _ },
      { rw [← mul_one (x j), pi.single_mul j (x j)],  exact ideal.mul_mem_left _ _ (this _ hj) } },
    { intro x, use pi.single i x, exact dif_pos rfl } },
  { rintros j ⟨q, rfl⟩, by_contra h, 
    apply q.2.1,
    rw [ideal.eq_top_iff_one, ← pi.single_eq_same j (1 : R j)],
    exact this _ h }
end

@[simps symm_apply] noncomputable
def prime_spectrum.pi_equiv {ι : Type*} [finite ι] (R : ι → Type*) [∀ i, comm_ring (R i)] :
  prime_spectrum (Π i, R i) ≃ Σ i, prime_spectrum (R i) :=
{ to_fun := λ p, ⟨_, p.pi_exists_unique.some_spec.1.some⟩,
  inv_fun := λ s, prime_spectrum.comap (pi.eval_ring_hom R s.1) s.2,
  left_inv := λ p, p.pi_exists_unique.some_spec.1.some_spec,
  right_inv := begin
    classical,
    refine function.right_inverse_of_injective_of_left_inverse _
      (λ p, p.pi_exists_unique.some_spec.1.some_spec),
    rintro ⟨s, ps⟩ ⟨t, pt⟩ e,
    dsimp at e,
    obtain ⟨i, hi, hi'⟩ := (prime_spectrum.comap (pi.eval_ring_hom R t) pt).pi_exists_unique,
    obtain ⟨rfl, rfl⟩ := ⟨hi' s ⟨ps, e⟩, hi' t ⟨pt, rfl⟩⟩,
    congr' 1,
    refine prime_spectrum.comap_injective_of_surjective _ _ e,
    exact λ x, ⟨pi.single t x, dif_pos rfl⟩
  end }

