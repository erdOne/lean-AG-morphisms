import dimension_theory.artinian
import dimension_theory.height

variables {R : Type*} [comm_ring R] (I : ideal R)

lemma ideal.is_maximal_iff_forall_is_prime {I : ideal R} : 
 I.is_maximal ↔ I ≠ ⊤ ∧ ∀ J, ideal.is_prime J → I ≤ J → I = J :=
begin
  refine ⟨λ H, ⟨H.ne_top,λ J hJ e, H.eq_of_le hJ.ne_top e⟩, λ H, _⟩,
  obtain ⟨m, hm, hm'⟩ := ideal.exists_le_maximal _ H.1,
  rwa H.2 m hm.is_prime hm',
end

lemma set.chain_height_le_one_iff {α : Type*} [preorder α] {s : set α} : 
  s.chain_height ≤ 1 ↔ is_antichain (<) s :=
begin
  split,
  { intros H x hx y hy e₁ e₂,
    suffices : ↑2 ≤ s.chain_height,
    { exact one_lt_two.not_le (with_top.coe_le_coe.mp $ this.trans H) },
    refine set.le_chain_height_iff.mpr ⟨[x, y], ⟨_, _⟩, rfl⟩; simp [hx, hy, e₂] },
  { intro H,
    rw [set.chain_height, supr₂_le_iff],
    rintros (_|⟨x, _|⟨y, l⟩⟩) ⟨_|⟨h₁, h₂⟩, h₃⟩; simp only [list.length, enat.coe_zero, zero_le,
      implies_true_iff, list.length_singleton, enat.coe_one, le_refl],
    refine (H (h₃ x _) (h₃ y _) h₁.ne h₁).elim; simp }
end

lemma set.chain_height_eq_one_iff {α : Type*} [preorder α] {s : set α} : 
  s.chain_height = 1 ↔ s.nonempty ∧ is_antichain (<) s :=
by rw [le_antisymm_iff, set.chain_height_le_one_iff, set.one_le_chain_height_iff, and_comm]

lemma krull_dimension_eq_zero_iff [nontrivial R] : 
  krull_dimension R = 0 ↔ (∀ (I : ideal R), I.is_prime → I.is_maximal) :=
begin
  rw [← nonpos_iff_eq_zero, ← with_top.add_le_add_iff_right (@with_top.one_ne_top ℕ _),
    zero_add, krull_dimension_succ, set.chain_height_le_one_iff],
  refine forall₂_congr (λ I hI, (ideal.is_maximal_iff_forall_is_prime.trans
    ((and_iff_right hI.ne_top).trans $ forall₂_congr $ λ J hJ, ⟨_, _⟩)).symm),
  { exact λ H e e', e (H e'.le) },
  { exact λ H e, not_not.mp (λ e', H e' (e.lt_of_ne e')) }
end

lemma is_artinian_ring_iff_krull_dimension_eq_zero [is_noetherian_ring R] [nontrivial R] : 
  is_artinian_ring R ↔ krull_dimension R = 0 :=
begin
  rw [is_artinian_ring_iff_is_noetherian_ring, and_iff_right ‹is_noetherian_ring R›,
    krull_dimension_eq_zero_iff],
end

lemma is_localization.is_noetherian_ring (I : ideal R) [I.is_prime] (A : Type*) [comm_ring A]
  [algebra R A] [is_localization.at_prime A I] [hR : is_noetherian_ring R] :
  is_noetherian_ring A :=
begin
  rw [is_noetherian_ring_iff, is_noetherian_iff_well_founded] at hR ⊢,
  exact order_embedding.well_founded (is_localization.order_embedding I.prime_compl A).dual hR
end

instance (I : ideal R) [I.is_prime] [is_noetherian_ring R] :
  is_noetherian_ring (localization.at_prime I) :=
is_localization.is_noetherian_ring I _

lemma is_artinian_ring.eq_maximal_ideal_of_is_prime [is_artinian_ring R] [local_ring R]
  (I : ideal R) [I.is_prime] : I = local_ring.maximal_ideal R :=
local_ring.eq_maximal_ideal (((is_artinian_ring_iff_is_noetherian_ring R).mp ‹_›).2 _ ‹_›)

lemma is_artinian_ring.radical_eq_maximal_ideal [is_artinian_ring R] [local_ring R]
  (I : ideal R) (hI : I ≠ ⊤) : I.radical = local_ring.maximal_ideal R :=
begin
  rw ideal.radical_eq_Inf,
  refine (Inf_le _).antisymm (le_Inf _),
  { exact ⟨local_ring.le_maximal_ideal hI, infer_instance⟩ },
  { rintros J ⟨h₁, h₂⟩, exactI (is_artinian_ring.eq_maximal_ideal_of_is_prime J).ge }
end

lemma ideal.is_prime.pow_le_iff {J : ideal R} (hJ : J.is_prime) {n : ℕ} (hn : n ≠ 0) : 
  I ^ n ≤ J ↔ I ≤ J :=
⟨λ H x hx, hJ.mem_of_pow_mem n (H (ideal.pow_mem_pow hx n)), (ideal.pow_le_self hn).trans⟩

lemma is_artinian_ring_iff_is_nilpotent_maximal_ideal [is_noetherian_ring R] [local_ring R] :
  is_artinian_ring R ↔ is_nilpotent (local_ring.maximal_ideal R) :=
begin
  split,
  { introI h,
    rw ← is_artinian_ring.radical_eq_maximal_ideal (⊥ : ideal R) bot_ne_top,
    exact is_artinian_ring.is_nilpotent_nilradical R },
  { rintro ⟨n, hn⟩,
    rcases eq_or_ne n 0 with (rfl|hn'),
    { rw pow_zero at hn, exact (one_ne_zero hn).elim },
    rw is_artinian_ring_iff_is_noetherian_ring,
    refine ⟨‹_›, λ I hI, _⟩,
    suffices : local_ring.maximal_ideal R ≤ I,
    { rw ← (local_ring.maximal_ideal.is_maximal R).eq_of_le hI.ne_top this, apply_instance },
    rw [← hI.pow_le_iff (local_ring.maximal_ideal R) hn', hn],
    exact bot_le }
end

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

lemma ideal.is_nilpotent_iff_le_nilradical {I : ideal R} (hI : I.fg) : 
  is_nilpotent I ↔ I ≤ nilradical R :=
⟨λ ⟨n, hn⟩ x hx, ⟨n, hn ▸ ideal.pow_mem_pow hx n⟩,
  λ h, ⟨_, le_bot_iff.mp (ideal.exists_pow_le_of_fg _ _ hI h).some_spec⟩⟩

namespace submodule

open ideal

variables {M : Type*} [add_comm_group M] [module R M]


/-- *Nakayama's Lemma** - A slightly more general version of (4) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `smul_sup_eq_of_le_smul_of_le_jacobson_bot` for the special case when `J = ⊥`.  -/
lemma smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson' {I J : ideal R}
  {N N' : submodule R M} (hN' : N'.fg) (hIJ : I ≤ jacobson J)
  (hNN : N' ≤ N ⊔ I • N') : N ⊔ N' = N ⊔ J • N' :=
begin
  replace hNN : N ⊔ N' ≤ N ⊔ I • N' := sup_le le_sup_left hNN,
  have hNN' : N ⊔ N' = N ⊔ I • N',
    from le_antisymm hNN
      (sup_le_sup_left (submodule.smul_le.2 (λ _ _ _, submodule.smul_mem _ _)) _),
  have h_comap := submodule.comap_injective_of_surjective (linear_map.range_eq_top.1 (N.range_mkq)),
  have : (I • N').map N.mkq = N'.map N.mkq,
  { rw ←h_comap.eq_iff,
    simpa [comap_map_eq, sup_comm, eq_comm] using hNN' },
  have := @submodule.eq_smul_of_le_smul_of_le_jacobson _ _ _ _ _ I J
    (N'.map N.mkq) (hN'.map _)
    (by rw [← map_smul'', this]; exact le_rfl)
    hIJ,
  rw [← map_smul'', ←h_comap.eq_iff, comap_map_eq, comap_map_eq, submodule.ker_mkq,
    sup_comm] at this,
  rw [this, sup_comm]
end

/-- *Nakayama's Lemma** - Statement (4) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson` for a generalisation
to the `jacobson` of any ideal -/
lemma smul_sup_le_of_le_smul_of_le_jacobson_bot' {I : ideal R}
  {N N' : submodule R M} (hN' : N'.fg) (hIJ : I ≤ jacobson ⊥)
  (hNN : N' ≤ N ⊔ I • N') : N' ≤ N :=
by rw [← sup_eq_left, smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson' hN' hIJ hNN,
  bot_smul, sup_bot_eq]

end submodule

lemma with_top.lt_coe_iff_add_one_le {n : ℕ} {m : ℕ∞} : 
  m < n ↔ m + 1 ≤ n :=
begin
  cases m; simp only [with_top.none_eq_top, with_top.some_eq_coe, ← with_top.coe_one,
    with_top.top_add, ← with_top.coe_add, with_top.coe_le_coe, with_top.coe_lt_coe,
    with_top.nat_ne_top, not_top_lt, top_le_iff, nat.lt_iff_add_one_le],
end

lemma ideal.height_le_iff {p : ideal R} {n : ℕ} [p.is_prime] :
  p.height ≤ n ↔ ∀ q : ideal R, q.is_prime → q < p → q.height < n :=
begin
  rw ideal.height_eq_prime_height,
  delta ideal.prime_height,
  rw [set.chain_height_eq_supr_Iic, supr₂_le_iff],
  simp only [set.mem_inter_iff, set.mem_set_of_eq, set.mem_Iio, and_imp],
  apply forall₃_congr,
  introsI q hq h,
  rw [with_top.lt_coe_iff_add_one_le, ideal.height_eq_prime_height, ideal.prime_height_succ,
    set.inter_assoc, set.inter_eq_right_iff_subset.mpr (set.Iic_subset_Iio.mpr h)]
end

lemma ideal.height_le_one_of_is_principal_of_mem_minimal_primes_of_local_ring [is_noetherian_ring R]
  [local_ring R] (I : ideal R) (hI : I.is_principal)
    (hp : (local_ring.maximal_ideal R) ∈ I.minimal_primes) :
    (local_ring.maximal_ideal R).height ≤ 1 :=
begin
  rw [← with_top.coe_one, ideal.height_le_iff],
  introsI q h₁ h₂,
  suffices : q.prime_height = 0, { rw [ideal.height_eq_prime_height, this], exact zero_lt_one },
  rw [← ideal.height_eq_prime_height,
    ← is_localization.at_prime.krull_dimension_eq_height q (localization.at_prime q),
    ← is_artinian_ring_iff_krull_dimension_eq_zero,
    is_artinian_ring_iff_is_nilpotent_maximal_ideal,
    ← localization.at_prime.map_eq_maximal_ideal],
  have hI : I ≠ ⊤ := (hp.1.2.trans_lt
    (lt_top_iff_ne_top.mpr (local_ring.maximal_ideal.is_maximal _).ne_top)).ne, 
  haveI := ideal.quotient.nontrivial hI,
  haveI := local_ring.of_surjective' I^.quotient.mk ideal.quotient.mk_surjective,
  have : is_artinian_ring (R ⧸ I),
  { rw [is_artinian_ring_iff_is_nilpotent_maximal_ideal,
      ideal.is_nilpotent_iff_le_nilradical
      (is_noetherian.noetherian _)],
    refine (ideal.comap_le_comap_iff_of_surjective
      I^.quotient.mk ideal.quotient.mk_surjective _ _).mp _,
    rw [nilradical, ideal.comap_radical, ideal.zero_eq_bot, ← ring_hom.ker_eq_comap_bot,
      ideal.mk_ker, local_ring.eq_maximal_ideal (ideal.comap_is_maximal_of_surjective
      I^.quotient.mk ideal.quotient.mk_surjective), ideal.radical_eq_Inf, le_Inf_iff],
    any_goals { apply_instance },
    exact λ J ⟨hJ₁, hJ₂⟩, hp.2 ⟨hJ₂, hJ₁⟩ (local_ring.le_maximal_ideal hJ₂.ne_top) },
  let f := algebra_map R (localization.at_prime q),
  let qs : ℕ →o (ideal (R ⧸ I))ᵒᵈ :=
  { to_fun := λ n, ((q.map f ^ n).comap f).map I^.quotient.mk,
    monotone' := λ i j e, ideal.map_mono (ideal.comap_mono (ideal.pow_le_pow e)) },
  obtain ⟨n, hn⟩ := (@well_founded.monotone_chain_condition (order_dual _) _).mp this.1 qs,
  refine ⟨n, (_ : q.map f ^ n = 0)⟩,
  apply submodule.eq_bot_of_le_smul_of_le_jacobson_bot (q.map f) _ (is_noetherian.noetherian _),
  rotate,
  { rw [local_ring.jacobson_eq_maximal_ideal, localization.at_prime.map_eq_maximal_ideal],
    exacts [le_rfl, bot_ne_top] },
  { apply_instance },
  rw [smul_eq_mul, ← pow_succ,
    ← is_localization.map_comap q.prime_compl (localization.at_prime q) (q.map f ^ n),
    ← is_localization.map_comap q.prime_compl (localization.at_prime q) (q.map f ^ (n + 1))],
  apply ideal.map_mono,
  refine submodule.smul_sup_le_of_le_smul_of_le_jacobson_bot' (is_noetherian.noetherian _)
    (_ : I ≤ _) _,
  { rw local_ring.jacobson_eq_maximal_ideal, exacts [hp.1.2, bot_ne_top] },
  specialize hn _ n.le_succ,
  apply_fun ideal.comap I^.quotient.mk at hn,
  simp only [qs, order_hom.coe_fun_mk, ← ring_hom.ker_eq_comap_bot, ideal.mk_ker,
    ideal.comap_map_of_surjective I^.quotient.mk ideal.quotient.mk_surjective] at hn,
  intros x hx,
  obtain ⟨y, hy, z, hz, rfl⟩ := submodule.mem_sup.mp ((hn.le : _) (ideal.mem_sup_left hx)),
  refine submodule.add_mem_sup hy _,
  obtain ⟨z, rfl⟩ := I^.is_principal.mem_iff_eq_smul_generator^.mp hz,
  rw [smul_eq_mul, smul_eq_mul, mul_comm],
  refine ideal.mul_mem_mul (submodule.is_principal.generator_mem _) _,
  rwa [ideal.mem_comap, f.map_add, smul_eq_mul, map_mul, ideal.add_mem_iff_right _
    (ideal.pow_le_pow n.le_succ hy), mul_comm, ideal.unit_mul_mem_iff_mem] at hx,
  refine is_localization.map_units _ ⟨_, show I^.is_principal.generator ∈ q.prime_compl, from _⟩,
  change I^.is_principal.generator ∉ (↑q : set R),
  rw [← set.singleton_subset_iff, ← ideal.span_le, ideal.span_singleton_generator],
  exact λ e, h₂.not_le (hp.2 ⟨h₁, e⟩ h₂.le),
end

lemma ideal.height_le_one_of_is_principal_of_mem_minimal_primes [is_noetherian_ring R]
    (I : ideal R) (hI : I.is_principal)
    (p : ideal R) (hp : p ∈ I.minimal_primes) :
    p.height ≤ 1 :=
begin
  haveI := hp.1.1,
  casesI subsingleton_or_nontrivial R,
  { exact (‹p.is_prime›.ne_top (subsingleton.elim _ _)).elim },
  let f := algebra_map R (localization.at_prime p),
  have := ideal.height_le_one_of_is_principal_of_mem_minimal_primes_of_local_ring
    (I.map f) ⟨⟨f I^.is_principal.generator, _⟩⟩ _,
  { rwa [is_localization.height p.prime_compl, localization.at_prime.comap_maximal_ideal] at this },
  { rw [← set.image_singleton, ← ideal.span, ← ideal.map_span, ideal.span_singleton_generator I] },
  { rwa [is_localization.minimal_primes_map p.prime_compl (localization.at_prime p) I,
      set.mem_preimage, localization.at_prime.comap_maximal_ideal] }
end

lemma exists_covby_of_lt {α : Type*} [partial_order α] [hα : well_founded_gt α]
  {x y : α} (e : x < y) : ∃ z, x ≤ z ∧ z ⋖ y :=
begin
  rw [well_founded_gt, is_well_founded_iff, well_founded.well_founded_iff_has_max'] at hα,
  obtain ⟨z, ⟨hxz, hzy⟩, hz⟩ := hα (set.Ico x y) ⟨x, le_rfl, e⟩, 
  exact ⟨z, hxz, hzy, λ c hzc hcy, hzc.ne (hz _ ⟨hxz.trans hzc.le, hcy⟩ hzc.le).symm⟩
end

lemma ideal.height_le_iff_covby {p : ideal R} {n : ℕ} [p.is_prime] [is_noetherian_ring R] :
  p.height ≤ n ↔ ∀ q : ideal R, q.is_prime → q < p →
    (∀ q' : ideal R, q'.is_prime → q < q' → ¬ q' < p) → q.height < n :=
begin
  rw ideal.height_le_iff, 
  split,
  { exact λ H q hq e _, H q hq e },
  { intros H q hq e,
    have := (order_embedding.subtype (λ I : ideal R, I.is_prime)).dual.well_founded
      (well_founded_submodule_gt R R),
    obtain ⟨⟨x, hx⟩, hqx, hxp⟩ :=
      @exists_covby_of_lt { I : ideal R // I.is_prime } _ ⟨this⟩ ⟨q, hq⟩ ⟨p, ‹_›⟩ e,
    exact (ideal.height_mono hqx).trans_lt
      (H _ hx hxp.1 (λ I hI e, hxp.2 (show subtype.mk x hx < ⟨I, hI⟩, from e))) }
end

lemma with_top.lt_one_iff_eq_zero {n : ℕ∞} :
  n < 1 ↔ n = 0 :=
begin
  cases n; simp [with_top.some_eq_coe, with_top.none_eq_top],
end

variables {S : Type*} [comm_ring S]

lemma ideal.minimal_primes_map_of_surjective {f : R →+* S} (hf : function.surjective f)
  (I : ideal R) :
  (I.map f).minimal_primes = ideal.map f '' (I ⊔ f.ker).minimal_primes :=
begin
  apply set.image_injective.mpr (ideal.comap_injective_of_surjective f hf),
  rw [← ideal.comap_minimal_primes_eq_of_surjective hf, ← set.image_comp,
    ideal.comap_map_of_surjective f hf],
  ext, split,
  { intro hx, refine ⟨x, hx, _⟩, refine (ideal.comap_map_of_surjective f hf _).trans _,
    rw [sup_eq_left, ← ring_hom.ker_eq_comap_bot], exact le_sup_right.trans hx.1.2 },
  { rintro ⟨x, hx, rfl⟩, convert hx, refine (ideal.comap_map_of_surjective f hf _).trans _,
    rw [sup_eq_left, ← ring_hom.ker_eq_comap_bot], exact le_sup_right.trans hx.1.2 },
end

lemma ideal.height_le_spanrank_of_mem_minimal_primes [is_noetherian_ring R]
    (I : ideal R) (p : ideal R) (hp : p ∈ I.minimal_primes) :
    p.height ≤ I.spanrank :=
begin
  classical,
  delta submodule.spanrank,
  rw le_infi_iff,
  rintro ⟨s, hs, hs'⟩,
  unfreezingI
  { induction hn : hs.to_finset.card using nat.strong_induction_on with n H generalizing R },
  haveI := hp.1.1,
  subst hs',
  cases n,
  { rw [finset.card_eq_zero, ← finset.coe_inj, hs.coe_to_finset, finset.coe_empty] at hn, 
    rw [hn, submodule.span_empty, ← minimal_primes,
      ← ideal.prime_height_eq_zero_iff, ← ideal.height_eq_prime_height] at hp, exact hp.le },
  rw [← @localization.at_prime.comap_maximal_ideal _ _ p, ← is_localization.height p.prime_compl],
  rw [← @localization.at_prime.comap_maximal_ideal _ _ p, ← set.mem_preimage,
    ← is_localization.minimal_primes_map p.prime_compl, ← ideal.span, ideal.map_span] at hp,
  let A' := localization p.prime_compl,
  let p' := local_ring.maximal_ideal A',
  let t := algebra_map R A' '' s,
  have ht : t.finite := hs.image _,
  replace hn : ht.to_finset.card ≤ n + 1,
  { rw (show ht.to_finset = hs.to_finset.image (algebra_map R A'), by { ext, simp }),
    exact finset.card_image_le.trans_eq hn },
  change p' ∈ (ideal.span t).minimal_primes at hp,
  show p'.height ≤ _,
  clear_value t, clear hs s,
  simp_rw [ideal.height_le_iff_covby, nat.succ_eq_add_one, with_top.lt_coe_iff_add_one_le,
    with_top.coe_add, with_top.coe_one, with_top.add_le_add_iff_right with_top.one_ne_top],
  introsI q hq hpq hq',
  obtain ⟨x, s, hxs, rfl, hxq⟩ : ∃ x s, x ∉ s ∧ t = insert x s ∧ x ∉ q,
  { have : ¬ t ⊆ q,
    { rw ← ideal.span_le, exact λ e, lt_irrefl _ ((hp.2 ⟨hq, e⟩ hpq.le).trans_lt hpq) },
    obtain ⟨x, hxt, hxq⟩ := set.not_subset.mp this,
    refine ⟨x, t \ {x}, λ e, e.2 rfl, _, hxq⟩,
    rw [set.insert_diff_singleton, set.insert_eq_of_mem hxt] },
  have : p' ≤ (q ⊔ ideal.span {x}).radical,
  { rw [ideal.radical_eq_Inf, le_Inf_iff],
    rintro J ⟨hJ, hJ'⟩, by_contra h, refine hq' J hJ' (lt_of_le_of_ne (le_sup_left.trans hJ) _)
      (lt_of_le_not_le (local_ring.le_maximal_ideal hJ'.ne_top) h),
    rintro rfl, apply hxq, apply hJ, apply ideal.mem_sup_right,
    exact submodule.mem_span_singleton_self _ },
  have h : ∀ z ∈ s, z ∈ (q ⊔ ideal.span {x}).radical,
  { have := hp.1.2.trans this, rw [ideal.span_le, set.insert_subset] at this, exact this.2 },
  replace h : ∀ z : s, ∃ (m : ℕ) (y ∈ q) (a : A'), y + a * x = z ^ m,
  { rintros ⟨z, hzs⟩,
    dsimp [ideal.radical] at h,
    simp only [submodule.mem_sup, ideal.mem_span_singleton'] at h,
    obtain ⟨m, y, hyq, _, ⟨a, rfl⟩, hy⟩ := h z hzs, exact ⟨m, y, hyq, a, hy⟩ },
  choose m y hyq a hy using h,
  let I' := ideal.span (set.range y),
  let f := I'^.quotient.mk,
  have hf : function.surjective f := ideal.quotient.mk_surjective,
  have hf' : ∀ z, f (y z) = 0,
  { intro z, rw [← ring_hom.mem_ker, ideal.mk_ker], exact ideal.subset_span ⟨z, rfl⟩ },
  have hI'q : I' ≤ q, { rw ideal.span_le, rintro _ ⟨z, rfl⟩, apply hyq },
  have hI'p' : I' ≤ p' := hI'q.trans hpq.le,
  have h := @@ideal.height_le_one_of_is_principal_of_mem_minimal_primes _ _ ((ideal.span {x}).map f)
    ⟨⟨algebra_map _ _ x, by { rw [ideal.map_span, set.image_singleton], refl }⟩⟩ (p'.map f) _,
  swap,
  { haveI : (p'.map f).is_prime := ideal.map_is_prime_of_surjective hf _,
    obtain ⟨p'', h₁, h₂⟩ := ideal.exists_minimal_primes_le 
      (show (ideal.span {x}).map f ≤ p'.map f, from _),
    have hxp'' : f x ∈ p'',
    { rw [← ideal.span_singleton_le_iff_mem, ← set.image_singleton, ← ideal.map_span],
      exact h₁.1.2 },
    convert h₁,
    refine (ideal.map_le_iff_le_comap.mpr
      (hp.2 ⟨@@ideal.is_prime.comap _ _ _ f h₁.1.1, _⟩ _)).antisymm h₂,
    { rw [ideal.span_le, set.insert_subset],
      refine ⟨hxp'', _⟩,
      { intros z hz,
        show f z ∈ p'',
        apply h₁.1.1.mem_of_pow_mem (m ⟨z, hz⟩),
        specialize hy ⟨z, hz⟩, rw subtype.coe_mk at hy,
        rw [← map_pow, ← hy, map_add, hf', zero_add, map_mul],
        exact ideal.mul_mem_left _ _ hxp'' } },
    { conv_rhs { rw [← sup_eq_left.mpr hI'p', ← @ideal.mk_ker _ _ I', ring_hom.ker_eq_comap_bot,
        ← ideal.comap_map_of_surjective f hf p'] },
      exact ideal.comap_mono h₂ },
    { apply ideal.map_mono, rw [ideal.span_singleton_le_iff_mem],
      exact hp.1.2 (ideal.subset_span (set.mem_insert x s)) },
    { rwa [ideal.mk_ker] } },
  have : q.map f < p'.map f,
  { refine lt_of_le_not_le (ideal.map_mono hpq.le) (λ e, _),
    have := @ideal.comap_mono _ _ _ _ _ _ f _ _ e,
    simp_rw [ideal.comap_map_of_surjective f hf, ← ring_hom.ker_eq_comap_bot, ideal.mk_ker,
      sup_eq_left.mpr hI'q, sup_eq_left.mpr (hI'q.trans hpq.le)] at this,
    exact lt_irrefl _(this.trans_lt hpq) },
  haveI : (p'.map f).is_prime := ideal.map_is_prime_of_surjective hf (by rwa ideal.mk_ker),
  haveI : (q.map f).is_prime := ideal.map_is_prime_of_surjective hf (by rwa ideal.mk_ker),
  haveI : (p'.map f).finite_height,
  { rw [ideal.finite_height_iff, ← lt_top_iff_ne_top],
    exact or.inr (h.trans_lt (with_top.coe_lt_top 1)) },
  rw ideal.height_eq_prime_height at h,
  have := (ideal.prime_height_strict_mono this).trans_le h,
  rw [with_top.lt_one_iff_eq_zero, ideal.prime_height_eq_zero_iff, minimal_primes,
    ← @ideal.map_bot A' (A' ⧸ I') _ _ _ _ f, ideal.minimal_primes_map_of_surjective hf,
    bot_sup_eq, ideal.mk_ker] at this,
  obtain ⟨q', hq₁, hq₂⟩ := this,
  obtain rfl : q = q',
  { apply_fun ideal.comap f at hq₂,
    simp_rw [ideal.comap_map_of_surjective f hf, ← ring_hom.ker_eq_comap_bot, ideal.mk_ker] at hq₂,
    rwa [sup_eq_left.mpr hI'q, sup_eq_left.mpr hq₁.1.2, eq_comm] at hq₂ },
  have : s.finite := ht.subset (set.subset_insert _ _), haveI := this.fintype,
  have H' : (@@set.finite_range y this.to_subtype).to_finset.card ≤ n,
  { transitivity this.to_finset.card,
    { convert @finset.card_image_le s _ finset.univ y _ using 1,
      { congr' 1, ext, simp },
      { rw [(finset.card_eq_iff_eq_univ finset.univ).mpr rfl, fintype.card_of_finset'], simp } },
    { rw [← nat.lt_add_one_iff],
      refine lt_of_lt_of_le _ hn,
      rw [set.finite.to_finset_insert, finset.card_insert_of_not_mem, nat.lt_add_one_iff],
      simpa using hxs } },
  refine (H _ _ _ _ hq₁ _ (@@set.finite_range _ this.to_subtype) rfl rfl).trans
    (with_top.coe_le_coe.mpr H'),
  rwa [nat.succ_eq_add_one, nat.lt_add_one_iff]
end 
.

lemma ideal.nonempty_minimal_primes {I : ideal R} : 
  I.minimal_primes.nonempty ↔ I ≠ ⊤ :=
by rw [← set.ne_empty_iff_nonempty, ne.def, ideal.minimal_primes_eq_empty_iff]

lemma ideal.height_le_spanrank [is_noetherian_ring R] (hI : I ≠ ⊤) : 
  I.height ≤ I.spanrank :=
begin
  obtain ⟨J, hJ⟩ := ideal.nonempty_minimal_primes.mpr hI,
  refine (infi₂_le J hJ).trans _,
  rw ← ideal.height_eq_prime_height,
  exact ideal.height_le_spanrank_of_mem_minimal_primes _ _ hJ,
end

instance ideal.finite_height_of_is_noetherian_ring [is_noetherian_ring R] : I.finite_height :=
begin
  rw [ideal.finite_height_iff_lt, or_iff_not_imp_left],
  intro e,
  refine (ideal.height_le_spanrank I e).trans_lt _,
  rw [lt_top_iff_ne_top, submodule.spanrank_ne_top_iff],
  exact is_noetherian.noetherian I
end

lemma exists_spanrank_eq_and_height_eq [is_noetherian_ring R] (I : ideal R) (hI : I ≠ ⊤) :
  ∃ J ≤ I, J.spanrank = I.height ∧ J.height = I.height :=
begin
  obtain ⟨J, hJ, e₁, e₂⟩ := exists_spanrank_le_and_le_height_of_le_height I _
    (enat.coe_to_nat_le_self I.height),
  rw [enat.coe_to_nat_eq_self.mpr (ideal.height_ne_top hI)] at e₁ e₂,
  refine ⟨J, hJ, e₁.antisymm (e₂.trans $ ideal.height_le_spanrank _ _),
    (ideal.height_mono hJ).antisymm e₂⟩,
  rintro rfl, exact hI (top_le_iff.mp hJ),
end

lemma ideal.height_le_iff_exists_minimal_primes [is_noetherian_ring R]
    (p : ideal R) [p.is_prime] (n : ℕ∞) :
    p.height ≤ n ↔ ∃ I : ideal R, p ∈ I.minimal_primes ∧ I.spanrank ≤ n :=
begin
  split,
  { intro h,
    obtain ⟨I, hI, e₁, e₂⟩ := exists_spanrank_eq_and_height_eq p ‹p.is_prime›.ne_top,
    refine ⟨I, _, e₁.symm ▸ h⟩,
    exact ideal.mem_minimal_primes_of_height_eq hI e₂.ge },
  { rintros ⟨I, h₁, h₂⟩, exact (ideal.height_le_spanrank_of_mem_minimal_primes _ _ h₁).trans h₂ }
end