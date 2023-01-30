import ring_theory.artinian
import ring_theory.ideal.operations
import algebra.module.torsion
import dimension_theory.length
import dimension_theory.noetherian
import dimension_theory.jacobson

variables (K : Type*) [field K] (R : Type*) [comm_ring R] [algebra K R] [algebra.finite_type K R]

lemma is_artinian_ring.is_field_of_is_domain [is_artinian_ring R] [h : nontrivial R] [is_domain R] :
  is_field R :=
begin
  refine ⟨h.1, mul_comm, _⟩,
  intros x hx,
  obtain ⟨n, y, hy⟩ := is_artinian.exists_pow_succ_smul_dvd x (1 : R),
  replace hy : x ^ n * (x * y - 1) = 0,
  { rw [mul_sub, sub_eq_zero], convert hy using 1, simp [nat.succ_eq_add_one, pow_add, mul_assoc] },
  rw [mul_eq_zero, sub_eq_zero] at hy,
  exact ⟨_, hy.resolve_left $ pow_ne_zero _ hx⟩
end

variables {R}

lemma is_artinian_ring.is_maximal_of_is_prime [is_artinian_ring R]
  (I : ideal R) [h : I.is_prime] : I.is_maximal :=
begin
  rw ← ideal.quotient.is_domain_iff_prime at h,
  rw ideal.quotient.maximal_ideal_iff_is_field_quotient,
  haveI : is_artinian_ring (R ⧸ I) :=
    function.surjective.is_artinian_ring ideal.quotient.mk_surjective,
  apply is_artinian_ring.is_field_of_is_domain,
end

lemma is_artinian_ring.is_maximal_iff_is_prime [is_artinian_ring R] (I : ideal R) :
  I.is_maximal ↔ I.is_prime :=
⟨ideal.is_maximal.is_prime, @@is_artinian_ring.is_maximal_of_is_prime _ _ I⟩

lemma is_artinian_ring.jacobson_eq_radical [is_artinian_ring R] (I : ideal R) :
  I.jacobson = I.radical :=
by simp_rw [ideal.jacobson, ideal.radical_eq_Inf, is_artinian_ring.is_maximal_iff_is_prime]

variables (R)

lemma is_artinian_ring.jacobson_eq_nilradical [is_artinian_ring R] :
  (⊥ : ideal R).jacobson = nilradical R :=
is_artinian_ring.jacobson_eq_radical _

lemma is_artinian_ring.is_nilpotent_nilradical [is_artinian_ring R] :
  is_nilpotent (nilradical R) :=
is_artinian_ring.jacobson_eq_nilradical R ▸ is_artinian_ring.is_nilpotent_jacobson_bot

variables {R}

lemma ideal.is_prime.inf_le_iff (I : ideal R) [hI : I.is_prime] (s : set (ideal R)) (hs : s.finite) :
  Inf s ≤ I ↔ ∃ J ∈ s, J ≤ I :=
begin
  refine ⟨_, λ ⟨J, H, e⟩, (Inf_le H).trans e⟩,
  apply set.finite.induction_on hs; clear hs s,
  { intro e, rw [Inf_empty, ← eq_top_iff] at e, exact ((hI.1 : _) e).elim },
  { intros J s h₁ hs H e,
    rw Inf_insert at e,
    by_cases Inf s ≤ I, { obtain ⟨K, hK, hK'⟩ := H h, exact ⟨K, set.mem_insert_of_mem _ hK, hK'⟩ },
    suffices : J ≤ I, { exact ⟨J, set.mem_insert _ _, this⟩ },
    change ¬ ∀ x ∈ Inf s, x ∈ I at h,
    push_neg at h,
    obtain ⟨x, hx, hx'⟩ := h,
    intros y hy,
    have := e (ideal.mul_le_inf (ideal.mul_mem_mul hy hx)),
    rw hI.mul_mem_iff_mem_or_mem at this,
    exact this.resolve_right hx' }
end

lemma ideal.is_prime.mem_of_Inf_eq (I : ideal R) [hI : I.is_prime]
  (s : set (ideal R)) (hs : s.finite) (H : Inf s = I) : I ∈ s :=
begin
  obtain ⟨J, hJ, e⟩ := (ideal.is_prime.inf_le_iff I s hs).mp H.le,
  exact e.antisymm (H.symm.trans_le $ Inf_le hJ) ▸ hJ
end

variables (R)

lemma is_artinian_ring.is_maximal_finite [H : is_artinian_ring R] :
  (set_of ideal.is_maximal : set $ ideal R).finite :=
begin
  nontriviality R,
  let S : set (ideal R) :=
  { J | ∃ s : set (ideal R), s.finite ∧ (∀ I ∈ s, ideal.is_maximal I) ∧ J = Inf s },
  obtain ⟨M, hM⟩ := ideal.exists_maximal R,
  have : S.nonempty := ⟨M, {M}, set.to_finite _, λ _ e, e.symm ▸ hM, Inf_singleton.symm⟩,
  obtain ⟨_, ⟨s, hs, hs', rfl⟩, h⟩ := set_has_minimal_iff_artinian.mpr H S this,
  convert hs,
  ext J,
  refine ⟨λ hJ, _, hs' J⟩,
  haveI : J.is_maximal := hJ,
  have : Inf s ≤ J,
  { rw [← inf_eq_right, ← Inf_insert],
    refine h _ ⟨_, hs.insert _, _, rfl⟩ (Inf_le_Inf $ set.subset_insert _ _),
    unfreezingI { rintros I (rfl|H') }, { apply_instance }, { exact hs' _ H' } },
  obtain ⟨M, hM, hM'⟩ := (ideal.is_prime.inf_le_iff J s hs).mp this,
  exact (hs' M hM).eq_of_le hJ.ne_top hM' ▸ hM,
end

lemma is_artinian_ring.is_prime_finite [H : is_artinian_ring R] :
  (set_of ideal.is_prime : set $ ideal R).finite :=
begin
  convert is_artinian_ring.is_maximal_finite R,
  ext,
  rw is_artinian_ring.is_maximal_iff_is_prime,
end

def submodule.order_iso_of_surjective {R S} (M) [comm_semiring R] [semiring S]
  [add_comm_monoid M] [algebra R S] [module S M] [module R M] [is_scalar_tower R S M]
  (h : function.surjective (algebra_map R S)) :
  submodule S M ≃o submodule R M :=
{ inv_fun := λ p,
  { smul_mem' := λ c x hx, by { obtain ⟨c, rfl⟩ := h c, simpa using p.smul_mem c hx }, ..p },
  left_inv := λ x, submodule.ext (λ _, iff.rfl),
  right_inv := λ x, submodule.ext (λ _, iff.rfl),
  ..submodule.restrict_scalars_embedding _ _ _ }

lemma is_noetherian_of_tower_of_surjective {R S} (M) [comm_semiring R] [semiring S]
  [add_comm_monoid M] [algebra R S] [module S M] [module R M] [is_scalar_tower R S M]
  (h : function.surjective (algebra_map R S)) :
  is_noetherian R M ↔ is_noetherian S M :=
begin
  refine ⟨is_noetherian_of_tower R, _⟩,
  simp_rw is_noetherian_iff_well_founded,
  exact (submodule.order_iso_of_surjective M h).symm.to_order_embedding.dual.well_founded
end

lemma is_artinian_of_tower_of_surjective {R S} (M) [comm_ring R] [comm_ring S]
  [add_comm_group M] [algebra R S] [module S M] [module R M] [is_scalar_tower R S M]
  (h : function.surjective (algebra_map R S)) :
  is_artinian R M ↔ is_artinian S M :=
begin
  refine ⟨is_artinian_of_tower R, _⟩,
  simp_rw is_artinian_iff_well_founded,
  exact (submodule.order_iso_of_surjective M h).symm.to_order_embedding.well_founded
end


instance (R) [ring R] (M) [add_comm_group M] [module R M]
  (N : submodule R M) [is_artinian R M] : is_artinian R (M ⧸ N) :=
is_artinian_of_surjective M (submodule.mkq N) (submodule.quotient.mk_surjective N)

lemma is_artinian_top_iff {M} [add_comm_group M] [module R M]:
  is_artinian R (⊤ : submodule R M) ↔ is_artinian R M :=
begin
  unfreezingI { split; assume h },
  { exact is_artinian_of_linear_equiv (linear_equiv.of_top (⊤ : submodule R M) rfl) },
  { exact is_artinian_of_linear_equiv (linear_equiv.of_top (⊤ : submodule R M) rfl).symm },
end

lemma is_noetherian_iff_is_artinian_of_mul (I J : ideal R) [I.is_maximal]
  (H : is_noetherian R (I * J : _) ↔ is_artinian R (I * J : _)) :
    is_noetherian R J ↔ is_artinian R J :=
begin
  let IJ := submodule.comap J.subtype (I * J),
  have : module.is_torsion_by_set R (↥J ⧸ IJ) I,
  { rintros x ⟨y, hy : y ∈ I⟩,
    obtain ⟨⟨x, hx⟩, rfl⟩ := submodule.mkq_surjective _ x,
    rw [subtype.coe_mk, ← map_smul, submodule.mkq_apply, submodule.quotient.mk_eq_zero],
    show _ ∈ I * J, by simpa using ideal.mul_mem_mul hy hx },
  letI : module (R ⧸ I) (J ⧸ IJ) := this.module,
  letI := ideal.quotient.field I,
  have : function.surjective (algebra_map R (R ⧸ I)) := ideal.quotient.mk_surjective,
  have : is_noetherian R (J ⧸ IJ) ↔ is_artinian R (J ⧸ IJ),
  { rw [is_noetherian_of_tower_of_surjective (J ⧸ IJ) this,
      (module.finite_length_tfae_of_field (R ⧸ I) (J ⧸ IJ)).out 1 2,
      ← is_artinian_of_tower_of_surjective (J ⧸ IJ) this] },
  split,
  { introI _,
    haveI := this.mp infer_instance,
    haveI : is_artinian R (I * J : _) := H.mp (is_noetherian_of_le ideal.mul_le_left),
    exact is_artinian_of_range_eq_ker
      (submodule.of_le (ideal.mul_le_left) : (I * J : _) →ₗ[R] J) IJ.mkq
      (submodule.of_le_injective _)
      (submodule.mkq_surjective _)
      (by simp [submodule.range_of_le]) },
  { introI _,
    haveI := this.mpr infer_instance,
    haveI : is_noetherian R (I * J : _) := H.mpr (is_artinian_of_le ideal.mul_le_left),
    exact is_noetherian_of_range_eq_ker
      (submodule.of_le (ideal.mul_le_left) : (I * J : _) →ₗ[R] J) IJ.mkq
      (submodule.of_le_injective _)
      (submodule.mkq_surjective _)
      (by simp [submodule.range_of_le]) },
end

lemma is_noetherian_iff_is_artinian_of_prod_eq_bot (s : multiset (ideal R))
  (hs : ∀ I ∈ s, ideal.is_maximal I) (h' : s.prod = ⊥) :
    is_noetherian_ring R ↔ is_artinian_ring R :=
begin
  rw [is_noetherian_ring_iff, ← is_noetherian_top_iff, is_artinian_ring_iff,
    ← is_artinian_top_iff],
  by_contra h,
  suffices : ¬ (is_noetherian R (⊥ : ideal R) ↔ is_artinian R (⊥ : ideal R)),
  { apply this, exact ⟨λ _, infer_instance, λ _, infer_instance⟩ },
  rw ← h', clear h',
  unfreezingI { induction s using multiset.induction with a s hs' },
  { rw [multiset.prod_zero, ideal.one_eq_top], exact h },
  { rw multiset.prod_cons,
    intro hs'',
    apply hs' (λ _ H, hs _ $ multiset.mem_cons_of_mem H),
    haveI := hs a (multiset.mem_cons_self a _),
    apply is_noetherian_iff_is_artinian_of_mul _ _ _ hs'' }
end

lemma is_artinian_ring.exists_multiset_ideal_is_maximal_and_prod_eq_bot
  (R : Type*) [comm_ring R] [is_artinian_ring R] :
  ∃ s : multiset (ideal R), (∀ I ∈ s, ideal.is_maximal I) ∧ s.prod = ⊥ :=
begin
  casesI subsingleton_or_nontrivial R, { exact ⟨∅, λ _ h, h.elim, subsingleton.elim _ _⟩ },
  obtain ⟨n, e⟩ := is_artinian_ring.is_nilpotent_nilradical R,
  have hn : n ≠ 0, { rintro rfl, apply @top_ne_bot (ideal R), simpa using e },
  refine ⟨n • (is_artinian_ring.is_prime_finite R).to_finset.1, _, _⟩,
  { intros I hI,
    rw [multiset.mem_nsmul hn, ← finset.mem_def, set.finite.mem_to_finset] at hI,
    rwa is_artinian_ring.is_maximal_iff_is_prime },
  { rw [multiset.prod_nsmul, eq_bot_iff, ← ideal.zero_eq_bot, ← e,
      nilradical_eq_Inf, finset.prod_val],
    apply ideal.pow_mono,
    refine ideal.prod_le_inf.trans (le_Inf $ λ I hI, finset.inf_le _),
    rwa set.finite.mem_to_finset }
end

lemma is_artinian_ring_iff_is_noetherian_ring :
  is_artinian_ring R ↔ is_noetherian_ring R ∧ ∀ I : ideal R, I.is_prime → I.is_maximal :=
begin
  casesI subsingleton_or_nontrivial R,
  { exact ⟨λ _, ⟨infer_instance, λ I h, (h.ne_top (subsingleton.elim _ _)).elim⟩,
      λ _, infer_instance⟩ },
  split,
  { introI H,
    obtain ⟨s, hs, hs'⟩ := is_artinian_ring.exists_multiset_ideal_is_maximal_and_prod_eq_bot R,
    have := is_noetherian_iff_is_artinian_of_prod_eq_bot _ s hs hs',
    simp_rw [is_artinian_ring.is_maximal_iff_is_prime, this], exact ⟨H, λ _ h, h⟩ },
  { rintros ⟨h₁, h₂⟩,
    resetI,
    obtain ⟨n, e⟩ := is_noetherian_ring.is_nilpotent_nilradical R,
    have hn : n ≠ 0, { rintro rfl, apply @top_ne_bot (ideal R), simpa using e },
    rwa ← is_noetherian_iff_is_artinian_of_prod_eq_bot _
      (n • (@minimal_primes_finite R _ _).to_finset.1) _ _,
    { simp_rw [multiset.mem_nsmul hn, ← finset.mem_def, set.finite.mem_to_finset],
      exact λ I hI, h₂ _ hI.1.1 },
    { rw [multiset.prod_nsmul, eq_bot_iff, ← ideal.zero_eq_bot, ← e, nilradical,
        ← ideal.Inf_minimal_primes, finset.prod_val],
      apply ideal.pow_mono,
      refine ideal.prod_le_inf.trans (le_Inf $ λ I hI, finset.inf_le _),
      rwa set.finite.mem_to_finset } }
end

lemma module.finite.trans' (R A B : Type*) [comm_semiring R] [comm_semiring A] [algebra R A]
  [add_comm_monoid B] [module R B] [module A B] [is_scalar_tower R A B] :
  ∀ [module.finite R A] [module.finite A B], module.finite R B
| ⟨⟨s, hs⟩⟩ ⟨⟨t, ht⟩⟩ := ⟨submodule.fg_def.2
  ⟨set.image2 (•) (↑s : set A) (↑t : set B),
    set.finite.image2 _ s.finite_to_set t.finite_to_set,
    by rw [set.image2_smul, submodule.span_smul hs (↑t : set B),
      ht, submodule.restrict_scalars_top]⟩⟩

lemma module.finite_of_tower (R S M : Type*) [comm_semiring R] [comm_semiring S] [add_comm_group M]
  [algebra R S] [module R M] [module S M] [is_scalar_tower R S M] [module.finite R S] :
  module.finite R M ↔ module.finite S M :=
⟨λ h, by exactI module.finite.of_restrict_scalars_finite R S M,
  λ h, by exactI module.finite.trans' R S M⟩

instance (I : ideal R) : module.finite R (R ⧸ I) :=
module.finite.of_surjective (ideal.quotient.mkₐ R I).to_linear_map ideal.quotient.mk_surjective

lemma linear_map.range_restrict_scalars {R S M N : Type*} [comm_semiring R] [semiring S]
  [add_comm_monoid M] [add_comm_monoid N] [algebra R S] [module R M] [module S M]
  [is_scalar_tower R S M] [module R N] [module S N] [is_scalar_tower R S N] (f : M →ₗ[S] N) : 
  (f.restrict_scalars R).range = f.range.restrict_scalars R := rfl


lemma is_artinian_of_is_artinian_of_mul_of_field (I J : ideal R) [I.is_maximal]
  [is_artinian R J] (H : is_artinian K (I * J : _)) : is_artinian K J :=
begin
  let IJ := submodule.comap J.subtype (I * J),
  have : module.is_torsion_by_set R (↥J ⧸ IJ) I,
  { rintros x ⟨y, hy : y ∈ I⟩,
    obtain ⟨⟨x, hx⟩, rfl⟩ := submodule.mkq_surjective _ x,
    rw [subtype.coe_mk, ← map_smul, submodule.mkq_apply, submodule.quotient.mk_eq_zero],
    show _ ∈ I * J, by simpa using ideal.mul_mem_mul hy hx },
  letI : module (R ⧸ I) (J ⧸ IJ) := this.module,
  letI := ideal.quotient.field I,
  have : function.surjective (algebra_map R (R ⧸ I)) := ideal.quotient.mk_surjective,
  haveI : algebra.finite_type K (R ⧸ I) := (‹algebra.finite_type K R›).trans infer_instance,
  haveI : module.finite K (R ⧸ I) := finite_of_finite_type_of_is_jacobson_of_field K (R ⧸ I),
  have : is_artinian R (J ⧸ IJ) ↔ is_artinian K (J ⧸ IJ),
  { rw [is_artinian_of_tower_of_surjective (J ⧸ IJ) this,
      (module.finite_length_tfae_of_field (R ⧸ I) (J ⧸ IJ)).out 2 0,
      (module.finite_length_tfae_of_field K (J ⧸ IJ)).out 2 0],
    exact (module.finite_of_tower K (R ⧸ I) (J ⧸ IJ)).symm },
  haveI := this.mp infer_instance,
  refine is_artinian_of_range_eq_ker
    ((submodule.of_le (ideal.mul_le_left) : (I * J : _) →ₗ[R] J).restrict_scalars K)
    (IJ.mkq.restrict_scalars K) _ _ _,
  { rw linear_map.coe_restrict_scalars, exact submodule.of_le_injective ideal.mul_le_left },
  { rw linear_map.coe_restrict_scalars, exact submodule.mkq_surjective IJ },
  simp only [submodule.ker_mkq, linear_map.ker_restrict_scalars, submodule.range_of_le,
    linear_map.range_restrict_scalars]
end

.

lemma is_artinian_ring_iff_is_artinian_of_field :
  is_artinian_ring R ↔ is_artinian K R :=
begin
  classical,
  refine ⟨_, is_artinian_of_tower K⟩,
  introI H, by_contra H',
  obtain ⟨s, hs, hs'⟩ := is_artinian_ring.exists_multiset_ideal_is_maximal_and_prod_eq_bot R,
  suffices : ¬ is_artinian K s.prod, { rw hs' at this, exact this infer_instance },
  clear hs',
  induction s using multiset.induction_on with a s h₁ h₂,
  { rw [multiset.prod_zero, ideal.one_eq_top], rwa ← is_artinian_top_iff at H' },
  { intro h₃, rw [multiset.prod_cons] at h₃,
    apply h₁ (λ I hI, hs I $ multiset.mem_cons_of_mem hI),
    haveI := hs a (multiset.mem_cons_self a s),
    exact is_artinian_of_is_artinian_of_mul_of_field _ _ a s.prod h₃ }
end

lemma is_artinian_ring_iff_finite_of_field :
  is_artinian_ring R ↔ module.finite K R :=
(is_artinian_ring_iff_is_artinian_of_field K R).trans
  ((module.finite_length_tfae_of_field K R).out 2 0)

lemma is_artinian_ring_iff_ring_hom_finite_of_field {K R : Type*} [field K] [comm_ring R]
  (f : K →+* R) (hf : f.finite_type) :
  is_artinian_ring R ↔ f.finite :=
@@is_artinian_ring_iff_finite_of_field K _ R _ f.to_algebra hf

lemma finite_iff_forall_prime_is_maximal_of_field :
  module.finite K R ↔ ∀ I : ideal R, I.is_prime → I.is_maximal :=
begin
  haveI := is_noetherian_ring_of_fg ‹algebra.finite_type K R›.1,
  haveI := is_noetherian_ring_of_surjective (⊤ : subalgebra K R) R
    subalgebra.top_equiv.to_ring_equiv.to_ring_hom subalgebra.top_equiv.surjective,
  rw [← is_artinian_ring_iff_finite_of_field K R, is_artinian_ring_iff_is_noetherian_ring],
  exact and_iff_right infer_instance
end
