import topology.category.Top.limits
import algebraic_geometry.prime_spectrum.basic


open_locale tensor_product

-- lemma prime_spectrum.zero_locus_map {R S : Type*} [comm_ring R] [comm_ring S] (f : R →+* S)
--   (I : ideal R) :
--   prime_spectrum.zero_locus ↑(I.map f) = prime_spectrum.zero_locus (f '' I) :=
-- prime_spectrum.zero_locus_span _

-- lemma ideal.radical_map_radical {R S : Type*} [comm_ring R] [comm_ring S] (f : R →+* S)
--   (I : ideal R) :
--   (I.radical.map f).radical = (I.map f).radical :=
-- begin
--   refine le_antisymm _ (ideal.radical_mono (ideal.map_mono ideal.le_radical)),
--   rw [ideal.radical_le_radical_iff, ideal.map_le_iff_le_comap, ideal.comap_radical],
--   exact ideal.radical_mono ideal.le_comap_map
-- end

-- lemma prime_spectrum.inducing_comap_iff {R S : Type*} [comm_ring R] [comm_ring S] (f : R →+* S) :
--   inducing (prime_spectrum.comap f) ↔ ∀ I : ideal S, I.radical = ((I.comap f).map f).radical :=
-- begin
--   split,
--   { intros h I,
--     obtain ⟨t, ht₁, ht₂⟩ := h.is_closed_iff.mp (prime_spectrum.is_closed_zero_locus I),
--     obtain ⟨J, rfl⟩ := (prime_spectrum.is_closed_iff_zero_locus_ideal t).mp ht₁,
--     apply_fun prime_spectrum.vanishing_ideal at ht₂,
--     simp only [compl_compl, prime_spectrum.preimage_comap_zero_locus,
--       ← prime_spectrum.zero_locus_map, prime_spectrum.vanishing_ideal_zero_locus_eq_radical] at ht₂,
--     rw [← ideal.radical_map_radical, ← ideal.comap_radical, ← ht₂,
--       ideal.comap_radical, ideal.radical_map_radical, ideal.map_comap_map] }, 
--   { intros H,
--     refine ⟨(prime_spectrum.comap f).2.le_induced.antisymm _⟩,
--     rintros s hs, rw [← is_open, ← is_closed_compl_iff, is_closed_induced_iff],
--     obtain ⟨I, hI⟩ :=
--       (prime_spectrum.is_closed_iff_zero_locus_ideal _).mp (is_closed_compl_iff.mpr hs),
--     refine ⟨_, prime_spectrum.is_closed_zero_locus (I.comap f), _⟩,
--     swap,
--     rw [hI, continuous_map.to_fun_eq_coe, prime_spectrum.preimage_comap_zero_locus,
--       ← prime_spectrum.zero_locus_map, ← prime_spectrum.zero_locus_radical, ← H,
--       prime_spectrum.zero_locus_radical] }
-- end

-- lemma prime_spectrum.inducing_comap_iff_forall_prime
--   {R S : Type*} [comm_ring R] [comm_ring S] (f : R →+* S) :
--   inducing (prime_spectrum.comap f) ↔
--     ∀ (I J : ideal S), I.comap f ≤ J.comap f → J.is_prime → I ≤ J :=
-- begin
--   refine (prime_spectrum.inducing_comap_iff f).trans (forall_congr $ λ I, _),
--   rw [← @antisymm_iff (ideal S) (≤), and_iff_left (ideal.radical_mono ideal.map_comap_le),
--     ideal.radical_le_radical_iff, ideal.radical_eq_Inf, le_Inf_iff],
--   simp [ideal.map_le_iff_le_comap]
-- end

-- lemma prime_spectrum.inducing_comap_iff_forall
--   {R S : Type*} [comm_ring R] [comm_ring S] (f : R →+* S) :
--   inducing (prime_spectrum.comap f) ↔
--     ∀ (x : S) (J : ideal S), J.is_prime → x ∉ J → ∃ y, x ∣ f y ∧ f y ∉ J :=
-- begin
--   rw prime_spectrum.inducing_comap_iff_forall_prime,
--   transitivity ∀ (x : S) (J : ideal S), (ideal.span {x}).comap f ≤ J.comap f → J.is_prime → x ∈ J,
--   { split,
--     { intros H x J hxJ hJ, have := H _ J hxJ hJ,
--       rwa [ideal.span_le, set.singleton_subset_iff] at this },
--     { intros H I J hIJ hJ x hx, refine H x J ((ideal.comap_mono _).trans hIJ) hJ,
--       rwa [ideal.span_le, set.singleton_subset_iff] } },
--   { simp_rw [@forall_swap _ (ideal.is_prime _), ← @not_imp_not (_ ∈ _), set_like.le_def],
--     refine forall₄_congr (λ x J hJ hxJ, _),
--     push_neg,
--     simp only [ideal.mem_comap, ideal.mem_span_singleton] }
-- end

-- lemma prime_spectrum.inducing_comap_iff_embedding
--   {R S : Type*} [comm_ring R] [comm_ring S] (f : R →+* S) :
--   inducing (prime_spectrum.comap f) ↔ embedding (prime_spectrum.comap f) :=
-- begin
--   refine ⟨λ h, ⟨h, λ I J e, _⟩, λ h, h.1⟩,
--   have : I.as_ideal.comap f = J.as_ideal.comap f := by injection e,
--   rw prime_spectrum.inducing_comap_iff_forall_prime at h,
--   exact le_antisymm (h _ _ this.le infer_instance) (h _ _ this.ge infer_instance),
-- end

noncomputable
abbreviation localization.at_prime.map {R S : Type*} [comm_ring R] [comm_ring S] (f : R →+* S)
  (p : ideal S) [p.is_prime] : 
  localization.at_prime (p.comap f) →+* localization.at_prime p :=
is_localization.map (localization.at_prime p) f
      (show (p.comap f).prime_compl ≤ p.prime_compl.comap f, from le_refl _)

instance {R S : Type*} [comm_ring R] [comm_ring S] (f : R →+* S)
  (p : ideal S) [p.is_prime] : is_local_ring_hom (localization.at_prime.map f p) :=
begin
  constructor,
  intros x hx,
  obtain ⟨x, s, rfl⟩ := is_localization.mk'_surjective (p.comap f).prime_compl x,
  rw [is_localization.map_mk', is_localization.at_prime.is_unit_mk'_iff _ p] at hx,
  rwa is_localization.at_prime.is_unit_mk'_iff _ (p.comap f),
end

def ring_hom.surjective_on_stalks {R S : Type*} [comm_ring R] [comm_ring S] (f : R →+* S) : Prop :=
∀ (p : ideal S) [p.is_prime], by exactI function.surjective (localization.at_prime.map f p)

-- lemma prime_spectrum.inducing_of_surjective_on_stalks
--   {R S : Type*} [comm_ring R] [comm_ring S] (f : R →+* S)
--   [is_domain S] (hf₂ : f.surjective_on_stalks) :
--   inducing (prime_spectrum.comap f) :=
-- begin
--   rw prime_spectrum.inducing_comap_iff_forall_prime,
--   introsI I J hI hJ x hx,
--   by_contra h,
--   obtain ⟨y, hy⟩ := (hf₂ J) (is_localization.mk' _ x (1 : J.prime_compl)),
--   obtain ⟨y, s, rfl⟩ := is_localization.mk'_surjective (J.comap f).prime_compl y,
--   rw [is_localization.map_mk', is_localization.mk'_eq_iff_eq, submonoid.coe_one, mul_one,
--     subtype.coe_mk, (is_localization.injective (localization.at_prime J)
--       J.prime_compl_le_non_zero_divisors).eq_iff] at hy,
--   apply J.prime_compl.mul_mem h s.prop,
--   rw ← hy,
--   apply hI,
--   show f y ∈ I,
--   rw hy,
--   exact ideal.mul_mem_right _ _ hx
-- end

lemma ring_hom.surjective_on_stalks_iff {R S : Type*} [comm_ring R] [comm_ring S] {f : R →+* S} :
  f.surjective_on_stalks ↔ ∀ (p : ideal S) (hp : p.is_prime) (x : S),
    ∃ y s c, f s ∉ p ∧ c ∉ p ∧ x * f s * c = f y * c :=
begin
  apply forall₂_congr,
  introsI J hJ,
  split,
  { introsI H x,
    obtain ⟨y, hy⟩ := H (is_localization.mk' _ x (1 : J.prime_compl)),
    obtain ⟨y, ⟨s, hs⟩, rfl⟩ := is_localization.mk'_surjective (J.comap f).prime_compl y,
    rw [is_localization.map_mk', is_localization.mk'_eq_iff_eq, submonoid.coe_one, mul_one,
      subtype.coe_mk, is_localization.eq_iff_exists J.prime_compl] at hy,
    obtain ⟨⟨c, hc⟩, e⟩ := hy,
    exact ⟨y, s, c, hs, hc, e.symm⟩ },
  { intros H x,
    obtain ⟨x, ⟨t, ht⟩, rfl⟩ := is_localization.mk'_surjective J.prime_compl x,
    obtain ⟨y, s, c, hs, hc, e⟩ := H x,
    obtain ⟨z, u, c', hu, hc', e'⟩ := H t,
    have : s * z ∈ (J.comap f).prime_compl,
    { rintro (h : f (s * z) ∈ J),
      apply J.prime_compl.mul_mem hs (mul_mem (mul_mem ht hu) hc'),
      rw [e', ← mul_assoc, ← map_mul],
      exact ideal.mul_mem_right _ _ h },
    refine ⟨is_localization.mk' _ (y * u) ⟨s * z, this⟩, _⟩,
    rw [is_localization.map_mk', is_localization.mk'_eq_iff_eq,
      is_localization.eq_iff_exists J.prime_compl],
    refine ⟨⟨_, J.prime_compl.mul_mem hc hc'⟩, _⟩,
    simp only [subtype.coe_mk, map_mul],
    transitivity (f y * c) * (t * f u * c'),
    { ring },
    { rw [← e, e'], ring } }
end

/-- `f : R →+* S` is surjective on stalks if every `x : S` can be written as 
`x = f a / f b` for some unit `f b`. In particular surjections and localizations
(and compositions of them) satisfy this condition. -/
lemma ring_hom.surjective_on_stalks_of_exists_eq_div
  {R S : Type*} [comm_ring R] [comm_ring S] {f : R →+* S}
  (hf : ∀ x : S, ∃ a b : R, is_unit (f b) ∧ x * f b = f a) : f.surjective_on_stalks :=
begin
  rw ring_hom.surjective_on_stalks_iff,
  introsI p hp x,
  obtain ⟨a, b, hb, e⟩ := hf x,
  refine ⟨a, b, 1, λ h, hp.1 (ideal.eq_top_of_is_unit_mem _ h hb), p.prime_compl.one_mem,
    by simpa only [mul_one]⟩,
end

lemma tensor_product_exists_of_surjective_on_stalks
  (R S T : Type*) [comm_ring R] [comm_ring S] [comm_ring T]
  [algebra R S] [algebra R T]
  (hf₂ : (algebra_map R T).surjective_on_stalks)
  (x : S ⊗[R] T) (J : ideal T) (hJ : J.is_prime) :
  ∃ (t : T) (r : R) a, (r • t ∉ J) ∧
    (1 : S) ⊗ₜ[R] (r • t) * x = a ⊗ₜ t :=
begin
  let g : T →+* S ⊗[R] T := ↑(algebra.tensor_product.include_right : T →ₐ[R] S ⊗ T),
  induction x using tensor_product.induction_on with x₁ x₂ x₁ x₂ hx₁ hx₂,
  { exact ⟨1, 1, 0, by { rw one_smul, exact J.prime_compl.one_mem },
      by rw [mul_zero, tensor_product.zero_tmul]⟩ },
  { obtain ⟨y, s, c, hs, hc, e⟩ :=
      ring_hom.surjective_on_stalks_iff.mp hf₂ J infer_instance x₂,
    simp_rw algebra.smul_def,
    refine ⟨c, s, y • x₁, J.prime_compl.mul_mem hs hc, _⟩,
    rw [mul_comm, algebra.tensor_product.tmul_mul_tmul, mul_one, ← mul_assoc, e,
      tensor_product.smul_tmul, algebra.smul_def] },
  { obtain ⟨t₁, r₁, a₁, hr₁, e₁⟩ := hx₁,
    obtain ⟨t₂, r₂, a₂, hr₂, e₂⟩ := hx₂,
    have : (r₁ * r₂) • (t₁ * t₂) = (r₁ • t₁) * (r₂ • t₂),
    { simp_rw [← smul_eq_mul], rw smul_smul_smul_comm },
    refine ⟨t₁ * t₂, r₁ * r₂, r₂ • a₁ + r₁ • a₂, this.symm ▸ J.prime_compl.mul_mem hr₁ hr₂, _⟩,
    rw [this, ← one_mul (1 : S), ← algebra.tensor_product.tmul_mul_tmul, mul_add, mul_comm (_ ⊗ₜ _),
      mul_assoc, e₁, algebra.tensor_product.tmul_mul_tmul, one_mul, smul_mul_assoc, 
      ← tensor_product.smul_tmul, mul_comm (_ ⊗ₜ _), mul_assoc, e₂, 
      algebra.tensor_product.tmul_mul_tmul, one_mul, smul_mul_assoc, ← tensor_product.smul_tmul,
      tensor_product.add_tmul, mul_comm t₁ t₂] }
end

-- lemma tensor_product_inducing_of_inducing_of_surjective_on_stalks
--   (R S T : Type*) [comm_ring R] [comm_ring S] [comm_ring T]
--   [algebra R S] [algebra R T] (hf : inducing (prime_spectrum.comap (algebra_map R T)))
--   (hf₂ : (algebra_map R T).surjective_on_stalks) :
--   inducing (prime_spectrum.comap (algebra_map S (S ⊗[R] T))) :=
-- begin
--   let g : T →+* S ⊗[R] T := ↑(algebra.tensor_product.include_right : T →ₐ[R] S ⊗ T),
--   rw prime_spectrum.inducing_comap_iff_forall at hf ⊢,
--   introsI x J hJ hxJ,
--   obtain ⟨t, r, a, ht, e⟩ := tensor_product_exists_of_surjective_on_stalks R S T hf₂ x (J.comap g)
--     infer_instance,
--   obtain ⟨y, ⟨c, hc⟩, hy⟩ := hf (r • t) (J.comap g) infer_instance ht,
--   refine ⟨y • a, ⟨1 ⊗ₜ[R] (r • t) * 1 ⊗ₜ[R] (r • c), _⟩, _⟩,
--   { rw [mul_left_comm, ← mul_assoc, e, algebra.tensor_product.tmul_mul_tmul, mul_one, mul_smul_comm,
--       ← smul_mul_assoc, ← hc, algebra.algebra_map_eq_smul_one y, ← tensor_product.smul_tmul],
--     refl },
--   { rintro (h : (y • a) ⊗ₜ[R] (1 : T) ∈ J),
--     apply J.prime_compl.mul_mem ht hxJ,
--     rw [tensor_product.smul_tmul, algebra.smul_def, ← one_mul a,
--       ← algebra.tensor_product.tmul_mul_tmul] at h,
--     have := ideal.mul_mem_right (1 ⊗ₜ t) _ ((hJ.mul_mem_iff_mem_or_mem.mp h).resolve_left hy),
--     rwa [algebra.tensor_product.tmul_mul_tmul, one_mul, mul_one, ← e] at this }
-- end

lemma tensor_product_surjective_on_stalks
  (R S T : Type*) [comm_ring R] [comm_ring S] [comm_ring T]
  [algebra R S] [algebra R T] (hf : (algebra_map R T).surjective_on_stalks) :
  (algebra_map S (S ⊗[R] T)).surjective_on_stalks :=
begin
  let g : T →+* S ⊗[R] T := ↑(algebra.tensor_product.include_right : T →ₐ[R] S ⊗ T),
  rw ring_hom.surjective_on_stalks_iff,
  introsI J hJ x,
  obtain ⟨t, r, a, ht, e⟩ := tensor_product_exists_of_surjective_on_stalks R S T hf x (J.comap g)
    infer_instance,
  refine ⟨a, algebra_map _ _ r, 1 ⊗ₜ (r • t), _, ht, _⟩,
  { rw [ideal.mem_comap, alg_hom.coe_to_ring_hom, map_smul,
      algebra.tensor_product.include_right_apply, algebra.smul_def,
      is_scalar_tower.algebra_map_apply R S (S ⊗[R] T)] at ht,
    exact λ h, ht (ideal.mul_mem_right _ _ h) },
  { rw [mul_comm, ← mul_assoc, e, algebra.tensor_product.algebra_map_apply,
      algebra.tensor_product.algebra_map_apply, algebra.tensor_product.tmul_mul_tmul, mul_one,
      algebra.tensor_product.tmul_mul_tmul, mul_one, one_mul, mul_comm, ← tensor_product.smul_tmul,
      algebra.id.map_eq_self, ← algebra.smul_def, algebra.id.map_eq_self] }
end

universe u

@[simps apply_coe_fst apply_coe_snd]
def prime_spectrum.tensor_product_to (R S T : Type u) [comm_ring R] [comm_ring S] [comm_ring T]
  [algebra R S] [algebra R T] :
  C(prime_spectrum (S ⊗[R] T), { x : prime_spectrum S × prime_spectrum T //
    prime_spectrum.comap (algebra_map R S) x.1 = prime_spectrum.comap (algebra_map R T) x.2 }) :=
begin
  refine (@Top.pullback_cone_is_limit (Top.of $ prime_spectrum S)
    (Top.of $ prime_spectrum T) (Top.of $ prime_spectrum R)
    (prime_spectrum.comap (algebra_map R S)) (prime_spectrum.comap (algebra_map R T))).lift
    (@category_theory.limits.pullback_cone.mk _ _ (Top.of $ prime_spectrum S)
    (Top.of $ prime_spectrum T) (Top.of $ prime_spectrum R)
    (prime_spectrum.comap (algebra_map R S)) (prime_spectrum.comap (algebra_map R T))
    (Top.of $ prime_spectrum (S ⊗[R] T))
    (prime_spectrum.comap $ algebra_map S (S ⊗[R] T))
    (prime_spectrum.comap $ ↑(algebra.tensor_product.include_right : T →ₐ[R] S ⊗ T)) _),
  ext1 s, 
  simp only [category_theory.coe_comp, function.comp_apply, ← prime_spectrum.comap_comp_apply,
    alg_hom.comp_algebra_map, ← is_scalar_tower.algebra_map_eq],
end

lemma prime_spectrum.le_of_tensor_product_to_eq
  (R S T : Type*) [comm_ring R] [comm_ring S] [comm_ring T]
  [algebra R S] [algebra R T]
  (hf : (algebra_map R T).surjective_on_stalks) (p₁ p₂ : prime_spectrum (S ⊗[R] T))
  (h : prime_spectrum.tensor_product_to R S T p₁ = prime_spectrum.tensor_product_to R S T p₂) :
  p₁ ≤ p₂ :=
begin
  let g : T →+* S ⊗[R] T := ↑(algebra.tensor_product.include_right : T →ₐ[R] S ⊗ T),
  intros x hxp₁,
  by_contra hxp₂,
  obtain ⟨t, r, a, ht, e⟩ := tensor_product_exists_of_surjective_on_stalks R S T hf x
    (p₂.as_ideal.comap g) infer_instance,
  have h₁ : a ⊗ₜ[R] t ∈ p₁.as_ideal := e ▸ p₁.as_ideal.mul_mem_left (1 ⊗ₜ[R] (r • t)) hxp₁,
  have h₂ : a ⊗ₜ[R] t ∉ p₂.as_ideal := e ▸ p₂.as_ideal.prime_compl.mul_mem ht hxp₂,
  rw [← mul_one a, ← one_mul t, ← algebra.tensor_product.tmul_mul_tmul] at h₁ h₂,
  have h₃ : t ∉ p₂.as_ideal.comap g,
  { intro h, apply h₂, exact ideal.mul_mem_left _ _ h },
  have h₄ : a ∉ p₂.as_ideal.comap (algebra_map S (S ⊗[R] T)),
  { intro h, apply h₂, exact ideal.mul_mem_right _ _ h },
  replace h₃ : t ∉ p₁.as_ideal.comap g,
  { apply_fun prime_spectrum.as_ideal ∘ prod.snd ∘ subtype.val at h,
    have : p₁.as_ideal.comap g = p₂.as_ideal.comap g := by convert h, rwa this },
  replace h₄ : a ∉ p₁.as_ideal.comap (algebra_map S (S ⊗[R] T)),
  { apply_fun prime_spectrum.as_ideal ∘ prod.fst ∘ subtype.val at h,
    have : p₁.as_ideal.comap (algebra_map S (S ⊗[R] T)) =
      p₂.as_ideal.comap (algebra_map S (S ⊗[R] T)) := by convert h, rwa this },
  { apply p₁.as_ideal.prime_compl.mul_mem h₄ h₃, exact h₁ }
end

lemma prime_spectrum.tensor_product_to_embedding
  (R S T : Type*) [comm_ring R] [comm_ring S] [comm_ring T]
  [algebra R S] [algebra R T]
  (hf : (algebra_map R T).surjective_on_stalks) :
  embedding (prime_spectrum.tensor_product_to R S T) :=
begin
  refine ⟨_, λ p₁ p₂ e, (prime_spectrum.le_of_tensor_product_to_eq R S T hf p₁ p₂ e).antisymm
    (prime_spectrum.le_of_tensor_product_to_eq R S T hf p₂ p₁ e.symm)⟩,
  let g : T →+* S ⊗[R] T := ↑(algebra.tensor_product.include_right : T →ₐ[R] S ⊗ T),
  refine ⟨(prime_spectrum.tensor_product_to R S T).2.le_induced.antisymm _⟩,
  delta subtype.topological_space,
  rw induced_compose,
  conv_rhs { rw prime_spectrum.is_basis_basic_opens.eq_generate_from },
  rw le_generate_from_iff_subset_is_open,
  rintros _ ⟨_, ⟨f, rfl⟩, rfl⟩,
  change is_open _,
  rw is_open_iff_forall_mem_open,
  rintros J (hJ : f ∉ J.as_ideal),
  obtain ⟨t, r, a, ht, e⟩ := tensor_product_exists_of_surjective_on_stalks R S T hf f
    (J.as_ideal.comap g) infer_instance,
  refine ⟨_, _, ⟨prime_spectrum.basic_open a ×ˢ prime_spectrum.basic_open t,
    prime_spectrum.is_open_basic_open.prod prime_spectrum.is_open_basic_open, rfl⟩, _⟩,
  { rintro x ⟨hx₁ : a ⊗ₜ[R] (1 : T) ∉ x.as_ideal, hx₂ : (1 : S) ⊗ₜ[R] t ∉ x.as_ideal⟩
      (hx₃ : f ∈ x.as_ideal),
    apply x.as_ideal.prime_compl.mul_mem hx₁ hx₂,
    rw [algebra.tensor_product.tmul_mul_tmul, mul_one, one_mul, ← e],
    exact x.as_ideal.mul_mem_left _ hx₃ },
  { have : a ⊗ₜ[R] (1 : T) * (1 : S) ⊗ₜ[R] t ∉ J.as_ideal,
    { rw [algebra.tensor_product.tmul_mul_tmul, mul_one, one_mul, ← e],
      exact J.as_ideal.prime_compl.mul_mem ht hJ },
    rwa [J.is_prime.mul_mem_iff_mem_or_mem.not, not_or_distrib] at this }
end
