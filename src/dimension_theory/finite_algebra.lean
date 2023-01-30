import algebraic_geometry.prime_spectrum.basic
import for_mathlib.residue_field
import dimension_theory.artinian

open_locale filter topological_space

open ideal (is_jacobson)

variables {K A : Type*} [field K] [comm_ring A] [algebra K A] [algebra.finite_type K A] 

lemma prime_spectrum.zero_locus_eq_iff {I J : ideal A} :
  prime_spectrum.zero_locus (I : set A) = prime_spectrum.zero_locus J ↔ I.radical = J.radical :=
begin
  split,
  { intro h, simp_rw [← prime_spectrum.vanishing_ideal_zero_locus_eq_radical, h] },
  { intro h, rw [← prime_spectrum.zero_locus_radical, h, prime_spectrum.zero_locus_radical] }
end

variable (K)

lemma ideal.exists_pow_le_of_fg {R : Type*} [comm_semiring R] (I J : ideal R) (h : I.fg)
  (h' : I ≤ J.radical) :
  ∃ n : ℕ, I ^ n ≤ J :=
begin
  revert h',
  refine submodule.fg_induction _ _ (λ I, I ≤ J.radical → ∃ n : ℕ, I ^ n ≤ J) _ _ _ h,
  { intros x hx, obtain ⟨n, hn⟩ := hx (ideal.subset_span (set.mem_singleton x)),
    exact ⟨n, by rwa [← ideal.span, ideal.span_singleton_pow, ideal.span_le, set.singleton_subset_iff]⟩ },
  { intros J K hJ hK hJK,
    obtain ⟨n, hn⟩ := hJ (λ x hx, hJK $ ideal.mem_sup_left hx),
    obtain ⟨m, hm⟩ := hK (λ x hx, hJK $ ideal.mem_sup_right hx),
    use n + m,
    rw [← ideal.add_eq_sup, add_pow, ideal.sum_eq_sup, finset.sup_le_iff],
    refine λ i hi, ideal.mul_le_right.trans _,
    obtain h | h := le_or_lt n i,
    { exact ideal.mul_le_right.trans ((ideal.pow_le_pow h).trans hn) },
    { refine ideal.mul_le_left.trans ((ideal.pow_le_pow _).trans hm),
      rw [add_comm, nat.add_sub_assoc h.le], apply nat.le_add_right } },
end

lemma ideal.exists_ne_zero_pow_le_of_fg {R : Type*} [comm_semiring R] (I J : ideal R) (h : I.fg)
  (h' : I ≤ J.radical) :
  ∃ n ≠ 0, I ^ n ≤ J :=
begin
  obtain ⟨n, hn⟩ := ideal.exists_pow_le_of_fg I J h h',
  exact ⟨n + 1, n.succ_ne_zero, (ideal.pow_le_pow n.le_succ).trans hn⟩,
end

lemma prime_spectrum.exists_closed_point_of_is_jacobson [is_jacobson A] 
  (s : set $ prime_spectrum A) (hs : is_open s) (hs' : s.nonempty) :
  ∃ x ∈ s, is_closed ({x} : set $ prime_spectrum A) :=
begin
  simp_rw prime_spectrum.is_closed_singleton_iff_is_maximal,
  obtain ⟨I, hI, hI'⟩ :=
    (prime_spectrum.is_closed_iff_zero_locus_radical_ideal _).mp hs.is_closed_compl,
  simp_rw [← @set.not_mem_compl_iff _ s, hI', prime_spectrum.mem_zero_locus],
  have := hs'.ne_empty, contrapose! this, simp_rw [not_imp_not] at this,
  rw [← set.compl_univ, eq_compl_comm, hI', eq_comm, ← prime_spectrum.zero_locus_bot,
    prime_spectrum.zero_locus_eq_iff, ideal.radical_eq_jacobson, ideal.radical_eq_jacobson],
  refine le_antisymm (le_Inf _) (ideal.jacobson_mono bot_le),
  rintro x ⟨-, hx⟩,
  exact Inf_le ⟨this ⟨x, hx.is_prime⟩ hx, hx⟩,
end

lemma prime_spectrum.is_compact_open_iff {s : set $ prime_spectrum A} :
  is_compact s ∧ is_open s ↔ 
  ∃ I : ideal A, I.fg ∧ (prime_spectrum.zero_locus (I : set A))ᶜ = s :=
begin
  rw topological_space.opens.is_compact_open_iff_eq_finite_Union_of_is_basis _
    prime_spectrum.is_basis_basic_opens prime_spectrum.is_compact_basic_open,
  simp_rw [prime_spectrum.basic_open_eq_zero_locus_compl, ← set.compl_Inter₂,
    ← prime_spectrum.zero_locus_Union, set.bUnion_of_singleton, @eq_comm _ s],
  split,
  { rintro ⟨s, hs, rfl⟩, 
    exact ⟨ideal.span s, ⟨hs.to_finset, by rw set.finite.coe_to_finset⟩,
      by rw prime_spectrum.zero_locus_span⟩ },
  { rintro ⟨_, ⟨s, rfl⟩, rfl⟩,
    exact ⟨s, s.finite_to_set, by rw [prime_spectrum.zero_locus_span]⟩ }
end

lemma prime_spectrum.exists_idempotent_basic_open_eq_of_is_clopen {s : set $ prime_spectrum A}
  (hs : is_clopen s) : 
  ∃ e : A, is_idempotent_elem e ∧ s = prime_spectrum.basic_open e :=
begin
  obtain ⟨I, hI, hI'⟩ := prime_spectrum.is_compact_open_iff.mp
    ⟨is_compact_of_is_closed_subset is_compact_univ hs.2 s.subset_univ, hs.1⟩,
  obtain ⟨J, hJ, hJ'⟩ := prime_spectrum.is_compact_open_iff.mp ⟨is_compact_of_is_closed_subset
    is_compact_univ hs.1.is_closed_compl $ set.subset_univ _, hs.2.is_open_compl⟩,
  simp only [compl_eq_iff_is_compl, ← eq_compl_iff_is_compl, compl_compl] at hI' hJ',
  have : I * J ≤ ideal.radical (⊥ : ideal A),
  { refine ideal.radical_le_radical_iff.mp (eq.le _),
    rw [← prime_spectrum.zero_locus_eq_iff, prime_spectrum.zero_locus_bot,
      prime_spectrum.zero_locus_mul, hI', hJ', set.compl_union_self] },
  obtain ⟨n, hn, hn'⟩ := ideal.exists_ne_zero_pow_le_of_fg _ _ (submodule.fg.mul hI hJ) this,
  rw mul_pow at hn',
  have : I ^ n ⊔ J ^ n = ⊤,
  { rw [eq_top_iff, ← ideal.span_pow_eq_top (I ∪ J : set A) _ n, ideal.span_le, set.image_union,
      set.union_subset_iff],
    split,
    { rintro _ ⟨x, hx, rfl⟩, exact ideal.mem_sup_left (ideal.pow_mem_pow hx n) },
    { rintro _ ⟨x, hx, rfl⟩, exact ideal.mem_sup_right (ideal.pow_mem_pow hx n) },
    { rw [ideal.span_union, ideal.span_eq, ideal.span_eq,
        ← prime_spectrum.zero_locus_empty_iff_eq_top, prime_spectrum.zero_locus_sup, hI', hJ',
        set.compl_inter_self] } },
  rw [ideal.eq_top_iff_one, submodule.mem_sup] at this,
  obtain ⟨x, hx, y, hy, e⟩ := this,
  refine ⟨x, _, subset_antisymm _ _⟩,
  { have : x * y = 0 := hn' (ideal.mul_mem_mul hx hy),
    rw ← eq_sub_iff_add_eq' at e, rwa [e, mul_sub, sub_eq_zero, eq_comm, mul_one] at this },
  { rw [prime_spectrum.basic_open_eq_zero_locus_compl, set.subset_compl_iff_disjoint_left,
      set.disjoint_iff_inter_eq_empty, ← hJ', ← prime_spectrum.zero_locus_span,
      ← prime_spectrum.zero_locus_sup, prime_spectrum.zero_locus_empty_iff_eq_top,
      ideal.eq_top_iff_one, ← e],
    exact submodule.add_mem_sup (ideal.subset_span $ set.mem_singleton _)
      (ideal.pow_le_self hn hy) },
  { rw [prime_spectrum.basic_open_eq_zero_locus_compl, set.compl_subset_comm, ← hI'],
    exact prime_spectrum.zero_locus_anti_mono
      (set.singleton_subset_iff.mpr $ ideal.pow_le_self hn hx) }
end

lemma prime_spectrum.basic_open_eq_zero_locus_of_is_idempotent_elem
  (e : A) (he : is_idempotent_elem e) : ↑(prime_spectrum.basic_open e) =
    prime_spectrum.zero_locus ({1 - e} : set A) :=
begin
  ext p,
  suffices : e ∉ p.as_ideal ↔ 1 - e ∈ p.as_ideal, { simpa },
  split,
  { intro h,
    refine (p.2.mem_or_mem_of_mul_eq_zero _).resolve_left h,
    rw [mul_sub, mul_one, he.eq, sub_self] },
  { intros h₁ h₂, apply p.2.1,
    rw [ideal.eq_top_iff_one, ← sub_add_cancel 1 e], exact add_mem h₁ h₂ }
end

lemma prime_spectrum.zero_locus_eq_basic_open_of_is_idempotent_elem
  (e : A) (he : is_idempotent_elem e) :
    prime_spectrum.zero_locus ({e} : set A) = prime_spectrum.basic_open (1 - e) :=
by rw [prime_spectrum.basic_open_eq_zero_locus_of_is_idempotent_elem _ he.one_sub, sub_sub_cancel]

lemma prime_spectrum.is_clopen_iff {s : set (prime_spectrum A)} :
  is_clopen s ↔ ∃ e : A, is_idempotent_elem e ∧ s = prime_spectrum.basic_open e :=
begin
  refine ⟨prime_spectrum.exists_idempotent_basic_open_eq_of_is_clopen, _⟩,
  rintro ⟨e, he, rfl⟩,
  refine ⟨(prime_spectrum.basic_open e).prop, _⟩,
  rw [prime_spectrum.basic_open_eq_zero_locus_of_is_idempotent_elem e he],
  exact prime_spectrum.is_closed_zero_locus _
end

lemma is_isolated_point_iff {α : Type*} [topological_space α] {x : α} : 
  𝓝[≠] x = ⊥ ↔ is_open ({x} : set α) :=
by rw [← is_closed_compl_iff, ← closure_subset_iff_is_closed, set.subset_compl_singleton_iff,
    mem_closure_iff_nhds_within_ne_bot, filter.not_ne_bot]

lemma is_localization.of_le_of_is_unit {R : Type*} 
  [comm_ring R] (A : Type*) [comm_ring A] [algebra R A] (M N : submonoid R) [is_localization M A]
  (h : M ≤ N) (h' : ∀ x ∈ N, is_unit (algebra_map R A x)) : is_localization N A :=
begin
  refine ⟨λ x, h' _ x.2, λ x, _, _⟩,
  { obtain ⟨⟨r, ⟨m, hm⟩⟩, e⟩ := is_localization.surj M x,
    exact ⟨⟨r, ⟨m, h hm⟩⟩, e⟩ },
  { intros x y,
    split,
    { rw is_localization.eq_iff_exists M, rintros ⟨⟨c, hc⟩, e⟩, exact ⟨⟨c, h hc⟩, e⟩ },
    { rintros ⟨⟨c, hc⟩, e⟩,
      apply_fun algebra_map R A at e,
      simpa only [map_mul, subtype.coe_mk, is_unit.mul_left_inj (h' _ hc)] using e } }
end

def minimal_primes.to_prime_spectrum : minimal_primes A ↪ prime_spectrum A :=
⟨λ x, ⟨x.1, x.2.1.1⟩, by tidy⟩ 

lemma minimal_primes.is_min_to_prime_spectrum (x : minimal_primes A) :
  is_min (minimal_primes.to_prime_spectrum x) :=
λ y h, x.2.2 ⟨y.2, bot_le⟩ h

lemma minimal_primes.range_to_prime_spectrum :
  set.range (@minimal_primes.to_prime_spectrum A _) = set_of is_min :=
begin
  apply subset_antisymm,
  { rintro _ ⟨x, rfl⟩, exact minimal_primes.is_min_to_prime_spectrum _ },
  { exact λ x hx, ⟨⟨x.as_ideal, ⟨x.2, bot_le⟩,
      λ y hy hy', @hx ⟨y, hy.1⟩ hy'⟩, subtype.coe_injective rfl⟩ },
end

lemma prime_spectrum.is_max_iff {x : prime_spectrum A} : 
  is_max x ↔ x.as_ideal.is_maximal :=
begin
  split,
  { intro hx,
    refine ⟨⟨x.2.ne_top, λ I hI, _⟩⟩,
    by_contra e,
    obtain ⟨m, hm, hm'⟩ := ideal.exists_le_maximal I e, 
    exact hx.not_lt (show x < ⟨m, hm.is_prime⟩, from hI.trans_le hm') },
  { intros hx y e, rw subtype.coe_injective (hx.eq_of_le y.2.ne_top e), exact le_rfl }
end

variable (K)

-- move me
lemma ideal.residue_field_bijective_of_maximal (I : ideal A) [I.is_maximal] :
  function.bijective (algebra_map (A ⧸ I) I.residue_field) :=
begin
  letI : field (A ⧸ I) := I^.quotient.field,
  exact (is_localization.at_units (A ⧸ I) (non_zero_divisors _) I.residue_field
    (λ x, is_unit_iff_ne_zero.mpr (mem_non_zero_divisors_iff_ne_zero.mp x.2))).bijective,
end

lemma ideal.residue_field_surjective_of_maximal (I : ideal A) [I.is_maximal] :
  function.surjective (algebra_map A I.residue_field) :=
begin
  rw is_scalar_tower.algebra_map_eq A (A ⧸ I) I.residue_field,
  exact I^.residue_field_bijective_of_maximal^.surjective^.comp ideal.quotient.mk_surjective
end

lemma prime_spectrum.is_min_iff_stable_under_generalization {x : prime_spectrum A} :
  is_min x ↔ stable_under_generalization ({x} : set $ prime_spectrum A) :=
begin
  simp_rw [stable_under_generalization, ← prime_spectrum.le_iff_specializes],
    exact ⟨λ H x' y h (e : x' = x), le_antisymm (e ▸ h) (@H y (e ▸ h)), λ H y h, (H h rfl).ge⟩
end

lemma prime_spectrum.is_closed_singleton_tfae_of_finite_type_of_field (x : prime_spectrum A) :
  tfae [x.as_ideal.is_maximal,
    is_closed ({x} : set $ prime_spectrum A),
    stable_under_specialization ({x} : set $ prime_spectrum A),
    module.finite K x.as_ideal.residue_field,
    algebra.is_algebraic K x.as_ideal.residue_field] :=
begin
  tfae_have : 1 ↔ 2,
  { rw prime_spectrum.is_closed_singleton_iff_is_maximal },
  tfae_have : 1 ↔ 3,
  { simp_rw [← prime_spectrum.is_max_iff, stable_under_specialization,
      ← prime_spectrum.le_iff_specializes],
    exact ⟨λ H x' y h (e : x' = x), (@H y (e ▸ h)).antisymm (e ▸ h), λ H y h, (H h rfl).le⟩ },
  tfae_have : 1 → 4,
  { introI h,
    haveI : algebra.finite_type K x.as_ideal.residue_field :=
      ‹algebra.finite_type K A›.trans (algebra.finite_type.of_surjective infer_instance
      (algebra.of_id _ _) x.as_ideal.residue_field_surjective_of_maximal),
    exact finite_of_finite_type_of_is_jacobson_of_field K x.as_ideal.residue_field },
  tfae_have : 4 → 5,
  { introI h, exact algebra.is_algebraic_of_finite _ _ },
  tfae_have : 5 → 1,
  { introI h,
    refine ideal.quotient.maximal_of_is_field _ _,
    apply (alg_equiv.of_injective
      ((is_scalar_tower.to_alg_hom A (A ⧸ x.as_ideal) x.as_ideal.residue_field).restrict_scalars K)
      (is_fraction_ring.injective (A ⧸ x.as_ideal) x.as_ideal.residue_field)).symm
      .to_ring_equiv.is_field_of_is_field,
    exact subalgebra.is_field_of_algebraic _ h },
  tfae_finish
end

lemma prime_spectrum.is_closed_singleton_iff_finite (x : prime_spectrum A) :
  is_closed ({x} : set $ prime_spectrum A) ↔ module.finite K x.as_ideal.residue_field :=
(prime_spectrum.is_closed_singleton_tfae_of_finite_type_of_field K x).out 1 3

open ideal (is_jacobson)

lemma prime_spectrum.is_open_singleton_tfae_of_finite_type_of_is_jacobson [is_jacobson A]
  [is_noetherian_ring A] (x : prime_spectrum A) :
  tfae [is_open ({x} : set $ prime_spectrum A),
    is_clopen ({x} : set $ prime_spectrum A),
    is_closed ({x} : set $ prime_spectrum A) ∧ is_min x] :=
begin
  tfae_have : 1 → 2,
  { intro h, obtain ⟨y, rfl : y = x, h'⟩ := prime_spectrum.exists_closed_point_of_is_jacobson _ h
      ⟨x, set.mem_singleton x⟩, exact ⟨h, h'⟩ },
  tfae_have : 2 → 3,
  { rw prime_spectrum.is_min_iff_stable_under_generalization,
    exact λ h, ⟨h.is_closed, h.is_open.stable_under_generalization⟩ },
  tfae_have : 3 → 1,
  { rintros ⟨h₁, h₂⟩,
    rw [prime_spectrum.is_closed_singleton_iff_is_maximal, ← prime_spectrum.is_max_iff] at h₁,
    suffices : {x} = (⋃ p ∈ { p : prime_spectrum A | is_min p ∧ p ≠ x },
      closure {p} : set (prime_spectrum A))ᶜ,
    { rw [this, is_open_compl_iff],
      refine is_closed_bUnion _ (λ _ _, is_closed_closure),
      haveI := (@minimal_primes_finite A _ _).to_subtype,
      apply (set.range $ @minimal_primes.to_prime_spectrum A _).to_finite.subset,
      rw minimal_primes.range_to_prime_spectrum,
      exact λ x hx, hx.1 },
    ext p,
    simp only [set.mem_singleton_iff, set.compl_Union₂, set.mem_Inter₂,
      set.mem_compl_iff, ← specializes_iff_mem_closure, ← prime_spectrum.le_iff_specializes],
    split,
    { rintro rfl y hy h, exact hy.2 (h₂.eq_of_le h) },
    { intros hp,
      apply h₁.eq_of_ge,
      obtain ⟨q, hq, hq'⟩ := ideal.exists_minimal_primes_le (@bot_le _ _ _ p.as_ideal),
      have : minimal_primes.to_prime_spectrum ⟨q, hq⟩ = x,
      { by_contra h, exact hp _ ⟨minimal_primes.is_min_to_prime_spectrum _, h⟩ hq' },
      rw ← this, exact hq' } },
  tfae_finish
end

lemma prime_spectrum.is_open_singleton_iff_is_max_and_is_min [ideal.is_jacobson A] 
  [is_noetherian_ring A]
  (x : prime_spectrum A) :
  is_open ({x} : set $ prime_spectrum A) ↔ is_max x ∧ is_min x :=
begin
  rw [(prime_spectrum.is_open_singleton_tfae_of_finite_type_of_is_jacobson x).out 0 2,
    prime_spectrum.is_closed_singleton_iff_is_maximal, prime_spectrum.is_max_iff],
end

lemma prime_spectrum.is_open_singleton_tfae_of_finite_type_of_field (x : prime_spectrum A) :
  tfae [is_open ({x} : set $ prime_spectrum A),
    is_clopen ({x} : set $ prime_spectrum A),
    module.finite K (localization.at_prime x.as_ideal),
    is_closed ({x} : set $ prime_spectrum A) ∧ is_min x] :=
begin
  haveI := is_jacobson_of_finite_type K A,
  haveI := algebra.finite_type.is_noetherian_ring K A,
  tfae_have : 1 ↔ 2,
  { exact (prime_spectrum.is_open_singleton_tfae_of_finite_type_of_is_jacobson x).out 0 1 },
  tfae_have : 1 ↔ 4,
  { exact (prime_spectrum.is_open_singleton_tfae_of_finite_type_of_is_jacobson x).out 0 2 },
  tfae_have : 2 → 3,
  { intro h,
    obtain ⟨e, he, he'⟩ := prime_spectrum.exists_idempotent_basic_open_eq_of_is_clopen h,
    have he'' : e ∈ x.as_ideal.prime_compl,
    { show x ∈ (prime_spectrum.basic_open e : set (prime_spectrum A)), rw ← he', exact rfl },
    haveI : is_localization.at_prime (localization.away e) x.as_ideal,
    { apply is_localization.of_le_of_is_unit _ (submonoid.powers e),
      { simpa only [set_like.mem_coe, submonoid.closure_le, set.singleton_subset_iff,
          submonoid.powers_eq_closure] },
      { intro a, dsimp [ideal.prime_compl], contrapose!, intro h,
        obtain ⟨I, hI₁, hI₂⟩ := exists_max_ideal_of_mem_nonunits h,
        suffices : prime_spectrum.comap (algebra_map A (localization.away e)) ⟨I, hI₁.is_prime⟩ = x,
        { rw ← this, exact hI₂ },
        rw [← set.mem_singleton_iff, he'],
        rintro (H : algebra_map A (localization.away e) e ∈ I),
        exact hI₁.ne_top (ideal.eq_top_of_is_unit_mem _ H
          (is_localization.map_units _ ⟨_, submonoid.mem_powers e⟩)) } },
    haveI : algebra.finite_type K (localization.at_prime x.as_ideal),
    { exact ‹algebra.finite_type K A›.trans ((algebra.finite_type.of_finite_presentation
        $ is_localization.away.finite_presentation e).equiv 
        (is_localization.alg_equiv x.as_ideal.prime_compl (localization.away e)
        (localization.at_prime x.as_ideal))) },
    rw finite_iff_forall_prime_is_maximal_of_field,
    intros I hI,
    suffices : I = local_ring.maximal_ideal _, { rw this, apply_instance },
    refine (is_localization.order_embedding x.as_ideal.prime_compl _).injective _,
    dsimp [is_localization.order_embedding],
    rw localization.at_prime.comap_maximal_ideal,
    suffices : prime_spectrum.comap (algebra_map A (localization.at_prime x.as_ideal)) ⟨I, hI⟩ = x,
    { conv_rhs { rw ← this }, refl },
    rw [← set.mem_singleton_iff, he'],
    rintro (H : algebra_map A (localization.at_prime x.as_ideal) e ∈ I),
    exact hI.ne_top (ideal.eq_top_of_is_unit_mem _ H (is_localization.map_units _ ⟨_, he''⟩)) },
  tfae_have : 3 → 4,
  { introI h,
    rw prime_spectrum.is_closed_singleton_iff_finite K x,
    haveI : is_scalar_tower K (localization.at_prime x.as_ideal) x.as_ideal.residue_field :=
      ideal.residue_field.is_scalar_tower x.as_ideal,
    refine ⟨module.finite.of_surjective (is_scalar_tower.to_alg_hom K
      (localization.at_prime x.as_ideal) _).to_linear_map ideal.quotient.mk_surjective, _⟩,
    intros y hy, 
    have : is_artinian_ring (localization.at_prime x.as_ideal) := is_artinian_of_tower K
      (((module.finite_length_tfae_of_field K (localization.at_prime x.as_ideal)).out 0 2).mp h),
    replace this := ((is_artinian_ring_iff_is_noetherian_ring _).mp this).2,
    have H : disjoint (x.as_ideal.prime_compl : set A) y.as_ideal,
    { show disjoint (x.as_idealᶜ : set A) y.as_ideal, rw disjoint_compl_left_iff, exact hy },
    show x.as_ideal ≤ y.as_ideal,
    rw [← @localization.at_prime.comap_maximal_ideal _ _ x.as_ideal,
      ← is_localization.comap_map_of_is_prime_disjoint _
        (localization.at_prime x.as_ideal) y.as_ideal y.2 H],
    refine ideal.comap_mono (local_ring.eq_maximal_ideal $ this _ _).ge,
    exact is_localization.is_prime_of_is_prime_disjoint x.as_ideal.prime_compl _ _ y.2 H },
  tfae_finish
end

.

lemma prime_spectrum.is_closed_singleton_iff_finite'
  {K A : Type*} [field K] [comm_ring A] (f : K →+* A) (hf : f.finite_type) (x : prime_spectrum A) :
  is_closed ({x} : set $ prime_spectrum A) ↔
    ((algebra_map A $ x.as_ideal.residue_field).comp f).finite :=
begin
  letI := f.to_algebra,
  haveI : algebra.finite_type K A := hf,
  exact prime_spectrum.is_closed_singleton_iff_finite K x
end

lemma _root_.list.tfae.of_subset {l₁ l₂ : list Prop} (e : l₁ ⊆ l₂) (h : tfae l₂) : tfae l₁ :=
λ a ha b hb, h _ (e ha) _ (e hb)

lemma prime_spectrum.is_closed_singleton_tfae_of_finite_type_of_field'
  {K A : Type*} [field K] [comm_ring A] (f : K →+* A) (hf : f.finite_type) (x : prime_spectrum A) :
  tfae [x.as_ideal.is_maximal,
    is_closed ({x} : set $ prime_spectrum A),
    stable_under_specialization ({x} : set $ prime_spectrum A),
    ((algebra_map A $ x.as_ideal.residue_field).comp f).finite] :=
begin
  letI := f.to_algebra,
  haveI : algebra.finite_type K A := hf,
  delta ring_hom.finite,
  refine (prime_spectrum.is_closed_singleton_tfae_of_finite_type_of_field K x).of_subset _,
  simp only [list.nil_subset, list.mem_cons_iff, true_or, or_true, list.mem_singleton,
    and_self, list.cons_subset, eq_self_iff_true],
end

lemma prime_spectrum.is_open_singleton_tfae_of_finite_type_of_field'
  {K A : Type*} [field K] [comm_ring A] (f : K →+* A) (hf : f.finite_type) (x : prime_spectrum A) :
  tfae [is_open ({x} : set $ prime_spectrum A),
    is_clopen ({x} : set $ prime_spectrum A),
    ((algebra_map A $ localization.at_prime x.as_ideal).comp f).finite,
    is_closed ({x} : set $ prime_spectrum A) ∧ is_min x] :=
begin
  letI := f.to_algebra,
  haveI : algebra.finite_type K A := hf,
  convert prime_spectrum.is_open_singleton_tfae_of_finite_type_of_field K x using 5,
  rw [← f.algebra_map_to_algebra, ← is_scalar_tower.algebra_map_eq],
  dsimp [ring_hom.finite],
  congr,
  exact (algebra.algebra_ext _ _ $ λ r, rfl),
end

open_locale tensor_product

universes u v w

lemma _root_.subalgebra.map_top {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]
  [algebra R S] [algebra R T] (f : S →ₐ[R] T) : (⊤ : subalgebra R S).map f = f.range := 
begin
  ext, simp,
end

instance {R S T : Type*} 
  [comm_ring R] [comm_ring S] [comm_ring T] [algebra R S] [algebra R T]
  [algebra.finite_type R T] : algebra.finite_type S (S ⊗[R] T) :=
begin
  classical,
  unfreezingI { obtain ⟨⟨s, hs⟩⟩ := ‹algebra.finite_type R T› },
  refine ⟨⟨s.image algebra.tensor_product.include_right, _⟩⟩,
  rw [finset.coe_image, ← @algebra.adjoin_adjoin_of_tower R S (tensor_product R S T),
    algebra.adjoin_image, hs, subalgebra.map_top, eq_top_iff],
  rintro x -,
  induction x using tensor_product.induction_on with x y x y hx hy,
  { exact zero_mem _ },
  { convert_to x • ((1 : S) ⊗ₜ y) ∈ _,
    { rw [tensor_product.smul_tmul', ← algebra.algebra_map_eq_smul_one], refl },
    { exact subalgebra.smul_mem _ (algebra.subset_adjoin ⟨y, rfl⟩) _ } },
  { exact add_mem hx hy }
end
