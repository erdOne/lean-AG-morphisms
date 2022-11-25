import ring_theory.is_tensor_product
import algebra.category.Ring.constructions
import category_theory.limits.shapes.kernel_pair

.

open category_theory

universe u

open_locale tensor_product

variables {R S : Type u} [comm_ring R] [comm_ring S]

lemma CommRing.epi_iff_bijective_include_right [algebra R S] :
  epi (CommRing.of_hom $ algebra_map R S) ↔
  function.bijective (algebra.tensor_product.include_right : S →ₐ[R] S ⊗ S) :=
begin
  let f := CommRing.of_hom (algebra_map R S),
  show epi f ↔ _,
  have : ‹algebra R S› = ring_hom.to_algebra f,
  { apply algebra.algebra_ext, intro r, refl },
  clear_value f, 
  unfreezingI { subst this },
  have := (is_pushout.of_is_colimit (CommRing.pushout_cocone_is_colimit f f)).op,
  show epi f ↔ _,
  split,
  { introI _,
    exact (@@as_iso _ _ $ (is_iso_op_iff _).mp (is_kernel_pair.is_iso_of_mono this))
      .CommRing_iso_to_ring_equiv.bijective },
  { intro h,
    exact @@category_theory.unop_epi_of_mono _ _ (@@is_kernel_pair.mono_of_is_iso_fst _ this
      ((is_iso_op_iff _).mpr $ show is_iso (ring_equiv.of_bijective _ h).to_CommRing_iso.hom,
      by apply_instance)) }
end

variable (R)

lemma module.exists_is_principal_quotient_of_finite (M : Type*) [add_comm_group M] [module R M]
  [module.finite R M] [nontrivial M] :
  ∃ N : submodule R M, N ≠ ⊤ ∧ submodule.is_principal (⊤ : submodule R (M ⧸ N))  :=
begin
  obtain ⟨n, f, hf⟩ := @module.finite.exists_fin R M _ _ _ _,
  let s := { m : ℕ | submodule.span R (f '' (coe ⁻¹' (set.Iio m))) ≠ ⊤ },
  have hns : ∀ x ∈ s, x < n,
  { intros x hx, dsimp [s] at hx, rw lt_iff_not_le, intro e, 
    have : (coe ⁻¹' set.Iio x : set (fin n)) = set.univ := by { ext y, simpa using y.2.trans_le e },
    simpa [this, hf] using hx },
  have hs₁ : s.nonempty := ⟨0, by { have : set.Iio 0 = ∅ := by { ext, simp }, simp [this] }⟩,
  have hs₂ : bdd_above s := ⟨n, λ x hx, (hns x hx).le⟩,
  have hs := nat.Sup_mem hs₁ hs₂,
  refine ⟨_, hs, ⟨⟨submodule.mkq _ (f ⟨_, hns _ hs⟩), _⟩⟩⟩,
  have := not_not.mp (not_mem_of_cSup_lt (order.lt_succ _) hs₂),
  rw [← set.image_singleton, ← submodule.map_span,
    ← (submodule.comap_injective_of_surjective (submodule.mkq_surjective _)).eq_iff,
    submodule.comap_map_eq, submodule.ker_mkq, submodule.comap_top, ← this, ← submodule.span_union,
    order.Iio_succ_eq_insert (Sup s), ← set.union_singleton, set.preimage_union, set.image_union,
    ← @set.image_singleton _ _ f, set.union_comm],
  { congr, ext, simp [fin.ext_iff] },
  { apply_instance }
end

lemma module.exists_surjective_quotient_of_finite (M : Type*) [add_comm_group M] [module R M]
  [module.finite R M] [nontrivial M] :
  ∃ (I : ideal R) (f : M →ₗ[R] R ⧸ I), I ≠ ⊤ ∧ function.surjective f :=
begin
  obtain ⟨N, hN, ⟨x, hx⟩⟩ := module.exists_is_principal_quotient_of_finite R M,
  let f := (linear_map.to_span_singleton R _ x).quot_ker_equiv_of_surjective
    (by rw [← linear_map.range_eq_top, ← linear_map.span_singleton_eq_range, hx]),
  refine ⟨_, f.symm.to_linear_map.comp N.mkq, _, f.symm.surjective.comp N.mkq_surjective⟩,
  intro e,
  obtain rfl : x = 0 := by simpa using linear_map.congr_fun (linear_map.ker_eq_top.mp e) 1,
  rw [ne.def, ← submodule.subsingleton_quotient_iff_eq_top, ← not_nontrivial_iff_subsingleton,
    not_not] at hN,
  resetI,
  simpa using hx,
end

variable {R}

lemma ring_hom.surjective_of_epi_of_finite (f : R →+* S) (h₁ : epi (CommRing.of_hom f)) 
  (h₂ : ring_hom.finite f) : function.surjective f :=
begin
  letI := f.to_algebra,
  haveI : module.finite R S := h₂,
  have h₃ := CommRing.epi_iff_bijective_include_right.mp h₁,
  let R' := (algebra.of_id R S).to_linear_map.range,
  have : subsingleton ((S ⧸ R') ⊗[R] (S ⧸ R')),
  { refine subsingleton_of_forall_eq 0 (λ y, _),
    induction y using tensor_product.induction_on with x y x y hx hy,
    { refl },
    { obtain ⟨x, rfl⟩ := R'.mkq_surjective x,
      obtain ⟨y, rfl⟩ := R'.mkq_surjective y,
      obtain ⟨z, hz⟩ := h₃.2 (x ⊗ₜ y),
      have : R'.mkq 1 = 0,
      { rw [← linear_map.mem_ker, submodule.ker_mkq], exact (algebra.of_id R S).range.one_mem },
      calc R'.mkq x ⊗ₜ R'.mkq y = tensor_product.map R'.mkq R'.mkq (x ⊗ₜ y) :
                (tensor_product.map_tmul R'.mkq R'.mkq x y).symm
        ... = tensor_product.map R'.mkq R'.mkq (algebra.tensor_product.include_right z) :
                by rw hz
        ... = R'.mkq 1 ⊗ₜ R'.mkq z : tensor_product.map_tmul R'.mkq R'.mkq 1 z
        ... = 0 ⊗ₜ R'.mkq z : by rw [this]
        ... = 0 : tensor_product.zero_tmul _ _ },
    { rw [hx, hy, zero_add] } },
  casesI subsingleton_or_nontrivial (S ⧸ R'),
  { show function.surjective (algebra.of_id R S).to_linear_map,
    rwa [← linear_map.range_eq_top, ← submodule.subsingleton_quotient_iff_eq_top] },
  haveI := module.finite.of_surjective _ R'.mkq_surjective,
  obtain ⟨I, ϕ, hI, hϕ⟩ := module.exists_surjective_quotient_of_finite R (S ⧸ R'),
  let ψ : (S ⧸ R') ⊗[R] (S ⧸ R') →ₗ[R] R ⧸ I := (algebra.tensor_product.lmul' R : _ →ₐ[R] R ⧸ I)
    .to_linear_map.comp (tensor_product.map ϕ ϕ),
  have : function.surjective ψ,
  { intro x, obtain ⟨x, rfl⟩ := hϕ x, obtain ⟨y, hy⟩ := hϕ 1, exact ⟨x ⊗ₜ y, by simp [hy]⟩ },
  have := this.subsingleton,
  rw submodule.subsingleton_quotient_iff_eq_top at this,
  contradiction
end