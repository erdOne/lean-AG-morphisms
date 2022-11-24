import ring_theory.local_properties
import for_mathlib.localized_module


section module

variables {R X Y : Type*} [comm_ring R]
variable (M : submonoid R)
variables [add_comm_group X] [module R X] [add_comm_group Y] [module R Y] (g : X →ₗ[R] Y)

lemma submodule.le_of_localization_maximal (M M' : submodule R X)
  (H : ∀ (J : ideal R) (hJ : J.is_maximal),
    by exactI M.localize J.prime_compl ≤ M'.localize J.prime_compl) : M ≤ M' :=
begin
  intros x hx,
  by_contradiction hx',
  have : (submodule.span R {M'.mkq x}).annihilator ≠ ⊤,
  { rwa [ne.def, submodule.annihilator_eq_top_iff, submodule.span_singleton_eq_bot,
      ← linear_map.mem_ker, submodule.ker_mkq] },
  obtain ⟨p, hp₁, hp₂⟩ := ideal.exists_le_maximal _ this,
  specialize H p hp₁,
  obtain ⟨y, hy, ⟨s, hs⟩, e⟩ := H (submodule.mem_localize_of_mem hx 1),
  obtain ⟨⟨u, hu⟩, e⟩ := localized_module.mk_eq.mp e,
  simp only [submonoid.smul_def, one_smul, smul_zero, subtype.coe_mk, @eq_comm X 0] at e,
  exact (mul_mem hu hs) (hp₂ $ by { rw [submodule.mem_annihilator_span_singleton, ← M'.mkq.map_smul,
    ← linear_map.mem_ker, submodule.ker_mkq, mul_smul, e], exact M'.smul_mem _ hy })
end

lemma submodule.eq_of_localization_maximal (M M' : submodule R X)
  (H : ∀ (J : ideal R) (hJ : J.is_maximal),
    by exactI M.localize J.prime_compl = M'.localize J.prime_compl) : M = M' :=
(submodule.le_of_localization_maximal _ _ $ by simp [H]).antisymm
  (submodule.le_of_localization_maximal _ _ $ by simp [H])

lemma submodule.eq_bot_of_localization_maximal (M : submodule R X)
  (H : ∀ (J : ideal R) (hJ : J.is_maximal),
    by exactI M.localize J.prime_compl = ⊥) : M = ⊥ :=
submodule.eq_of_localization_maximal _ _ (by simp [H])

lemma submodule.eq_top_of_localization_maximal (M : submodule R X)
  (H : ∀ (J : ideal R) (hJ : J.is_maximal),
    by exactI M.localize J.prime_compl = ⊤) : M = ⊤ :=
submodule.eq_of_localization_maximal _ _ (by simp [H])

lemma module.subsingleton_of_localization_maximal (X : Type*) [add_comm_group X] [module R X]
  (H : ∀ (J : ideal R) (hJ : J.is_maximal),
    by exactI subsingleton (localized_module J.prime_compl X)) : subsingleton X :=
begin
  simp_rw [← submodule.subsingleton_iff R, ← subsingleton_iff_bot_eq_top, @eq_comm _ ⊥] at ⊢,
  apply submodule.eq_bot_of_localization_maximal,
  exact λ J hJ, subsingleton.elim _ _
end

lemma module.eq_zero_of_localization_maximal (x : X)
  (H : ∀ (J : ideal R) (hJ : J.is_maximal),
    by exactI localized_module.mk x (1 : J.prime_compl) = 0) : x = 0 :=
begin
  rw ← @submodule.span_singleton_eq_bot R,
  apply submodule.eq_bot_of_localization_maximal,
  simp_rw [submodule.localize_eq_span, submodule.map_span, set.image_singleton,
    submodule.span_span_of_tower, submodule.span_singleton_eq_bot],
  exact H
end

include g

lemma linear_map.injective_of_localization_maximal
  (H : ∀ (J : ideal R) (hJ : J.is_maximal),
    by exactI function.injective (localized_module.map J.prime_compl g)) : function.injective g :=
begin
  rw ← linear_map.ker_eq_bot,
  apply submodule.eq_bot_of_localization_maximal,
  introsI J hJ,
  rw [linear_map.ker, ← submodule.localize_comap_map, submodule.localize_bot, submodule.comap_bot,
    linear_map.ker_eq_bot],
  exact H J hJ
end

lemma linear_map.surjective_of_localization_maximal
  (H : ∀ (J : ideal R) (hJ : J.is_maximal),
    by exactI function.surjective (localized_module.map J.prime_compl g)) : function.surjective g :=
begin
  rw ← linear_map.range_eq_top,
  apply submodule.eq_top_of_localization_maximal,
  introsI J hJ,
  rw [linear_map.range_eq_map, ← submodule.localize_map_map, submodule.localize_top,
    submodule.map_top, linear_map.range_eq_top],
  exact H J hJ
end

lemma linear_map.bijective_of_localization_maximal
  (H : ∀ (J : ideal R) (hJ : J.is_maximal),
    by exactI function.bijective (localized_module.map J.prime_compl g)) : function.bijective g :=
⟨linear_map.injective_of_localization_maximal g (λ J hJ, (H J hJ).1),
  linear_map.surjective_of_localization_maximal g (λ J hJ, (H J hJ).2)⟩

lemma linear_map.injective_localized_module_map (h : function.injective g) :
  function.injective (localized_module.map M g) :=
by rw [← linear_map.ker_eq_bot, linear_map.ker, ← submodule.localize_bot M,
  submodule.localize_comap_map, submodule.comap_bot, linear_map.ker_eq_bot.mpr h,
  submodule.localize_bot]

lemma linear_map.surjective_localized_module_map (h : function.surjective g) :
  function.surjective (localized_module.map M g) :=
by rw [← linear_map.range_eq_top, linear_map.range_eq_map, ← submodule.localize_top M,
  submodule.localize_map_map, submodule.map_top, linear_map.range_eq_top.mpr h,
  submodule.localize_top]

lemma linear_map.bijective_localized_module_map (h : function.bijective g) :
  function.bijective (localized_module.map M g) :=
⟨linear_map.injective_localized_module_map M g h.1,
  linear_map.surjective_localized_module_map M g h.2⟩

end module