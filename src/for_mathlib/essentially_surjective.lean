-- import ring_theory.localization.localization_localization
-- import ring_theory.local_properties

-- variables {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T] (f : R →+* S) (g : S →+* T)

-- def ring_hom.essentially_surjective (f : R →+* S) : Prop :=
-- ∀ x : S, ∃ a b : R, is_unit (f b) ∧ x * f b = f a

-- lemma is_localization.range_lift_is_unit_submonoid_map {x} : 
--   x ∈ (is_localization.lift (λ x : (is_unit.submonoid S).comap f, x.2) :
--     localization ((is_unit.submonoid S).comap f) →+* S).range ↔ 
--     ∃ a b : R, is_unit (f b) ∧ x * f b = f a :=
-- begin
--   split,
--   { rintro ⟨x, rfl⟩,
--     obtain ⟨x, s, rfl⟩ := is_localization.mk'_surjective ((is_unit.submonoid S).comap f) x,
--     refine ⟨x, s, s.2, _⟩,
--     rw [mul_comm, is_localization.lift_mk', ← mul_assoc, units.mul_inv_eq_iff_eq_mul, mul_comm],
--     refl },
--   { rintro ⟨a, b, hb, e⟩,
--     refine ⟨is_localization.mk' _ a ⟨b, show b ∈ (is_unit.submonoid S).comap f, from hb⟩, _⟩,
--     rw [is_localization.lift_mk', units.mul_inv_eq_iff_eq_mul, eq_comm, ← e], refl }
-- end

-- def fraction_subring : subring S :=
-- { ..(is_localization.lift (λ x : (is_unit.submonoid S).comap f, x.2) :
--   localization ((is_unit.submonoid S).comap f) →+* S).range.copy
--   { x | ∃ a b : R, is_unit (f b) ∧ x * f b = f a }
--   (set.ext $ λ x, (is_localization.range_lift_is_unit_submonoid_map f).symm) }

-- variables (R S)

-- def fraction_subalgebra [algebra R S] : subalgebra R S :=
-- { algebra_map_mem' := λ x, ⟨x, 1, (algebra_map R S).map_one.symm ▸ is_unit_one,
--     by rw [map_one, mul_one]⟩,
--   ..(fraction_subring $ algebra_map R S) }

-- variables {R S}

-- namespace ring_hom.essentially_surjective

-- variable {f}

-- lemma iff_surjective_comp_localization : f.essentially_surjective ↔ 
--   ∃ (M : submonoid R) (hM : ∀ x : M, is_unit (f x)),
--     function.surjective (is_localization.lift hM : localization M →+* S) :=
-- begin
--   split,
--   { intro H,
--     refine ⟨(is_unit.submonoid S).comap f, λ x, x.2, λ x, _⟩,
--     obtain ⟨a, b, hb, e⟩ := H x,
--     refine ⟨is_localization.mk' _ a ⟨b, show b ∈ (is_unit.submonoid S).comap f, from hb⟩, _⟩,
--     rw [is_localization.lift_mk', units.mul_inv_eq_iff_eq_mul, eq_comm, ← e],
--     refl },
--   { rintro ⟨M, hM, hM'⟩ x,
--     obtain ⟨x, rfl⟩ := hM' x,
--     obtain ⟨x, s, rfl⟩ := is_localization.mk'_surjective M x,
--     refine ⟨x, s, hM s, _⟩,
--     rw [mul_comm, is_localization.lift_mk', ← mul_assoc, units.mul_inv_eq_iff_eq_mul, mul_comm],
--     refl }
-- end

-- lemma iff_fraction_subring_eq_top :
--   f.essentially_surjective ↔ fraction_subring f = ⊤ :=
-- begin
--   rw eq_top_iff,
--   exact ⟨λ h x _, h x, λ h x, h trivial⟩
-- end

-- lemma of_surjective (hf : function.surjective f) :
--   f.essentially_surjective :=
-- begin
--   intro x, obtain ⟨x, rfl⟩ := hf x, refine ⟨x, 1, _, _⟩; simp only [map_one, mul_one, is_unit_one]
-- end

-- variable (S)

-- lemma of_localization [algebra R S] (M : submonoid R) [is_localization M S] :
--   (algebra_map R S).essentially_surjective :=
-- begin
--   intro x,
--   obtain ⟨⟨y, s⟩, e⟩ := is_localization.surj M x,
--   exact ⟨y, s, is_localization.map_units _ s, e⟩,
-- end

-- variables {S f g}

-- lemma comp (hg : g.essentially_surjective) (hf : f.essentially_surjective) :
--   (g.comp f).essentially_surjective :=
-- begin
--   intro x,
--   obtain ⟨y, s, hs, e₁⟩ := hg x, 
--   obtain ⟨z, t, ht, e₂⟩ := hf y, 
--   obtain ⟨u, v, hv, e₃⟩ := hf s, 
--   refine ⟨z * v, t * u, _, _⟩,
--   { apply_fun g at e₃, simp only [ring_hom.comp_apply, map_mul] at e₃ ⊢, rw ← e₃,
--     exact (ht.map g).mul (hs.mul $ hv.map g) },
--   { apply_fun g at e₂ e₃, simp only [ring_hom.comp_apply, map_mul] at e₂ e₃ ⊢,
--     rw [← e₂, ← e₃, ← e₁], simp only [mul_assoc, mul_comm, mul_left_comm], rw mul_comm (g (f t)) }
-- end

-- lemma tensor_product [algebra R S] [algebra R T] (h : (algebra_map R T).essentially_surjective) :
--   (algebra_map S (tensor_product R S T)).essentially_surjective :=
-- begin
--   rw iff_surjective_comp_localization at h ⊢,
--   obtain ⟨M, hM, hM'⟩ := h,
--   refine ⟨M.map (algebra_map R S), _, _⟩,
--   { rintro ⟨_, x, hx, rfl⟩, rw [subtype.coe_mk, ← is_scalar_tower.algebra_map_apply,
--     ← algebra.tensor_product.include_right.comp_algebra_map, ring_hom.comp_apply],
--     exact (hM ⟨x, hx⟩).map _ },
--   { intro x,
--     induction x using tensor_product.induction_on with x y x y hx hy,
--     { exact ⟨0, map_zero _⟩ },
--     { obtain ⟨y, rfl⟩ := hM' y,
--       obtain ⟨y, s, rfl⟩ := is_localization.mk'_surjective M y,
--       refine ⟨is_localization.mk' _ (y • x)
--         ⟨_, submonoid.mem_map_of_mem (algebra_map R S) s.prop⟩, _⟩,
--       rw [is_localization.lift_mk', units.mul_inv_eq_iff_eq_mul,
--         is_unit.coe_lift_right],
--       simp only [algebra.tensor_product.tmul_mul_tmul, set_like.coe_mk, mul_one,
--         algebra.id.map_eq_id, ring_hom.coe_monoid_hom, ring_hom.to_monoid_hom_eq_coe,
--         algebra.tensor_product.algebra_map_apply, ring_hom.id_apply, monoid_hom.restrict_apply,
--         ring_hom_comp_triple.comp_apply, mul_comm x, ← algebra.smul_def, tensor_product.smul_tmul],
--       rw [algebra.smul_def, algebra.smul_def, mul_one,
--         mul_comm, is_localization.lift_mk', mul_assoc],
--       erw is_unit.lift_right_inv_mul,
--       rw mul_one },
--   { obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := ⟨hx, hy⟩, exact ⟨x + y, map_add _ _ _⟩ } }
-- end

-- variables (f g)

-- lemma of_comp (h : (g.comp f).essentially_surjective) :
--   g.essentially_surjective :=
-- begin
--   rw iff_surjective_comp_localization at h ⊢,
--   obtain ⟨M, hM, hM'⟩ := h,
--   refine ⟨M.map f, _, _⟩,
--   { rintros ⟨_, x, hx, rfl⟩, exact hM ⟨x, hx⟩ },
--   { intro x,
--     obtain ⟨x, rfl⟩ := hM' x,
--     obtain ⟨x, s, rfl⟩ := is_localization.mk'_surjective M x,
--     refine ⟨is_localization.mk' _ (f x) ⟨_, submonoid.mem_map_of_mem f s.prop⟩, _⟩,
--     rw [is_localization.lift_mk', units.mul_inv_eq_iff_eq_mul, 
--       mul_comm, is_localization.lift_mk', ← mul_assoc, units.eq_mul_inv_iff_mul_eq],
--     simp only [ring_hom.to_monoid_hom_eq_coe, function.comp_app, ring_hom.coe_comp,
--       is_unit.coe_lift_right, set_like.coe_mk, ring_hom.coe_monoid_hom,
--       monoid_hom.restrict_apply],
--     exact mul_comm _ _ }
-- end

-- noncomputable
-- abbreviation localization.at_prime.map (p : ideal S) [p.is_prime] : 
--   localization.at_prime (p.comap f) →+* localization.at_prime p :=
-- is_localization.map (localization.at_prime p) f
--       (show (p.comap f).prime_compl ≤ p.prime_compl.comap f, from le_refl _)

-- lemma iff_stalk :
--   f.essentially_surjective ↔ ∀ (p : ideal S) [p.is_prime], 
--     by exactI function.surjective (localization.at_prime.map f p) :=
-- begin
--   split,
--   sorry; { introsI H p hp x,
--     have : ((localization.at_prime.map f p).comp (algebra_map R _)).essentially_surjective,
--     { rw is_localization.map_comp,
--       exact (of_localization _ p.prime_compl).comp H },
--     replace this := of_comp _ _ this,
--     obtain ⟨a, b, hb, e⟩ := this x,
--     obtain ⟨a, s, rfl⟩ := is_localization.mk'_surjective (p.comap f).prime_compl a,
--     obtain ⟨b, t, rfl⟩ := is_localization.mk'_surjective (p.comap f).prime_compl b,
--     replace hb : b ∈ (ideal.comap f p).prime_compl,
--     { rwa [is_localization.map_mk', is_localization.at_prime.is_unit_mk'_iff] at hb },
--     refine ⟨is_localization.mk' _ (a * t) ⟨_, mul_mem s.prop hb⟩, _⟩,
--     rw [is_localization.map_mk', is_localization.map_mk',
--       is_localization.eq_mk'_iff_mul_eq, mul_right_comm, ← (is_localization.map_units
--       (localization.at_prime p) ⟨f t, show f t ∈ p.prime_compl, from t.2⟩).mul_left_inj, mul_assoc,
--       mul_comm (is_localization.mk' _ _ _), is_localization.mul_mk'_eq_mk'_of_mul] at e,
--     erw is_localization.mk'_mul_cancel_left at e,
--     simp_rw [subtype.coe_mk, mul_assoc, ← map_mul] at e,
--     rw [is_localization.map_mk', is_localization.mk'_eq_iff_eq_mul, ← e],
--     refl },
--   { intros H x,
--     have : ∀ (p : ideal S) [p.is_prime], ∃ a ∉ p.comap f, f a * x ∈ f.range,
--     { introsI p hp,
--       obtain ⟨y, hy⟩ := H p (is_localization.mk' _ x (1 : p.prime_compl)),
--       obtain ⟨y, s, rfl⟩ := is_localization.mk'_surjective (p.comap f).prime_compl y,
--       rw [is_localization.map_mk', is_localization.mk'_eq_iff_eq, submonoid.coe_one,
--         mul_one, subtype.coe_mk, is_localization.eq_iff_exists p.prime_compl] at hy,
--     } 

--   }
-- end

-- end ring_hom.essentially_surjective

-- lemma ring_hom.localization_essentially_surjective :
--   ring_hom.localization_preserves @ring_hom.essentially_surjective :=
-- begin
--   introsI R S _ _ f M R' S' _ _ _ _ _ _ hf,
--   apply ring_hom.essentially_surjective.of_comp (algebra_map R R'),
--   rw is_localization.map_comp,
--   exact (ring_hom.essentially_surjective.of_localization _ $ M.map f).comp hf,
-- end

-- lemma ring_hom.essentially_surjective_of_localization_span :
--   ring_hom.of_localization_span @ring_hom.essentially_surjective :=
-- begin
--   -- rw ring_hom.of_localization_span_target_iff_finite,
--   introsI R S _ _ f s hs H x,
--   letI := f.to_algebra,
--   apply (fraction_subalgebra R S).to_submodule.mem_of_span_eq_top_of_smul_pow_mem _ hs,
--   intros r,
--   replace H := (H r).comp (ring_hom.essentially_surjective.of_localization
--     (localization.away (r : R)) (submonoid.powers (r : R))),
--   delta localization.away_map is_localization.away.map at H,
--   rw is_localization.map_comp at H,
--   obtain ⟨a, b, hb, e⟩ := H (algebra_map _ _ x),
--   simp only [ring_hom.comp_apply, ← map_mul] at e,
--   obtain ⟨⟨_, n, rfl⟩, e'⟩ := (is_localization.eq_iff_exists (submonoid.powers (f r)) _).mp e,
--   have : ∃ m : ℕ, is_unit (f (b * r ^ m)),
--   { obtain ⟨c, ⟨_, m, rfl⟩, hc⟩ := is_localization.mk'_surjective
--       (submonoid.powers (f r)) (↑(hb.unit⁻¹) : localization.away (f r)),
--     rw [← mul_one (↑(hb.unit⁻¹) : localization.away (f r)), units.eq_inv_mul_iff_mul_eq,
--       is_unit.unit_spec, ring_hom.comp_apply, is_localization.mul_mk'_eq_mk'_of_mul,
--       is_localization.mk'_eq_iff_eq_mul, one_mul, subtype.coe_mk, is_localization.eq_iff_exists
--         (submonoid.powers $ f r)] at hc,
--     have := is_localization.at_prime.is_unit_to_map_iff,
--     refine ⟨m, is_unit_of_mul_eq_one _ c _⟩,

--    },

--   have := is_localization.at_prime.is_unit_mk'_iff,
--   refine ⟨n, a * r ^ n, _⟩,
-- end


-- lemma ring_hom.essentially_surjective_is_local :
--   ring_hom.property_is_local @ring_hom.essentially_surjective :=
-- begin
--   constructor,
-- end

-- lemma ring_hom.essentially_surjective_of_localization_span :
--   ring_hom.of_localization_span @ring_hom.essentially_surjective :=
-- begin
--   introsI R S _ _ f s hs H,
--   letI := f.to_algebra,
--   apply (integral_closure R S).to_submodule.mem_of_span_eq_top_of_smul_pow_mem _ hs,
--   intros r,
--   letI := (localization.away_map f r).to_algebra,
--   haveI : is_scalar_tower R (localization.away (r : R)) (localization.away $ f r) := 
--     is_scalar_tower.of_algebra_map_eq' (is_localization.map_comp _).symm,
--   haveI : is_scalar_tower R S (localization.away $ f r) := 
--     is_scalar_tower.of_algebra_map_eq' rfl,
--   obtain ⟨⟨_, n, rfl⟩, p, hp, hp'⟩ := is_integral.exists_multiple_integral_of_is_localization
--     (submonoid.powers (r : R)) _ (H r (algebra_map _ _ x)),
--   simp only [submonoid.smul_def, subtype.coe_mk, algebra.smul_def, ring_hom.comp_apply,
--     is_scalar_tower.algebra_map_eq R S (localization.away $ f r), ← map_mul] at hp',
--   rw [eval₂_eq_eval_map, ← map_map, eval_map, eval₂_at_apply, ← @is_localization.mk'_one _ _
--     (submonoid.powers $ f r), is_localization.mk'_eq_zero_iff] at hp',
--   obtain ⟨⟨_, m, rfl⟩, H'⟩ := hp',
--   rw [subtype.coe_mk, mul_comm, ← map_pow, ← ring_hom.algebra_map_to_algebra f,
--     eval_map, ← eval₂_smul] at H',
--   by_cases (r : R) ^ m = 0, { use m, rw [h, zero_smul], exact zero_mem _ },
--   have hp'' : ((r : R) ^ m • p).leading_coeff = (r : R) ^ m,
--   { have hp'' : ((r : R) ^ m • p).coeff p.nat_degree = (r : R) ^ m,
--     { rw [coeff_smul, coeff_nat_degree, hp.leading_coeff, smul_eq_mul, mul_one] },
--     have : ((r : R) ^ m • p).nat_degree = p.nat_degree,
--     { exact (nat_degree_smul_le _ _).antisymm (le_nat_degree_of_ne_zero $ hp''.trans_ne h) },
--     rw [leading_coeff, this, hp''] },
--   have := is_integral_leading_coeff_smul _ _ H',
--   rw [hp'', ← algebra.smul_def, smul_smul, ← pow_add] at this,
--   exact ⟨m+n, this⟩
-- end
