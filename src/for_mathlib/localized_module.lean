import algebra.module.localized_module


section algebra

lemma is_localized_module.mk_of_algebra {R S S' : Type*} [comm_ring R] [comm_ring S] [comm_ring S']
  [algebra R S] [algebra R S'] (M : submonoid R) (f : S →ₐ[R] S')
  (h₁ : ∀ x ∈ M, is_unit (algebra_map R S' x))
  (h₂ : ∀ y, ∃ (x : S × M), x.2 • y = f x.1)
  (h₃ : ∀ x, f x = 0 → ∃ m : M, m • x = 0) :
  is_localized_module M f.to_linear_map :=
begin
  replace h₃ := λ x, iff.intro (h₃ x) (λ ⟨⟨m, hm⟩, e⟩, (h₁ m hm).mul_left_cancel $
    by { rw ← algebra.smul_def, simpa [submonoid.smul_def] using f.congr_arg e }),
  constructor,
  { intro x,
    rw module.End_is_unit_iff,
    split,
    { rintros a b (e : x • a = x • b), simp_rw [submonoid.smul_def, algebra.smul_def] at e,
      exact (h₁ x x.2).mul_left_cancel e },
    { intro a, refine ⟨((h₁ x x.2).unit⁻¹ : _) * a, _⟩, change (x : R) • (_ * a) = _,
      rw [algebra.smul_def, ← mul_assoc, is_unit.mul_coe_inv, one_mul] } },
  { exact h₂ },
  { intros, dsimp, rw [eq_comm, ← sub_eq_zero, ← map_sub, h₃], simp_rw [smul_sub, sub_eq_zero] },
end

end algebra

namespace is_localized_module

universes u v
variables {R : Type*} [comm_ring R] (S : submonoid R)
variables {M M' M'' : Type*} [add_comm_monoid M] [add_comm_monoid M'] [add_comm_monoid M'']
variables [module R M] [module R M'] [module R M''] (f : M →ₗ[R] M') (g : M →ₗ[R] M'')

variable [is_localized_module S f]


@[simp]
lemma iso_mk (m : M) (s : S) :
  is_localized_module.iso S f (localized_module.mk m s) = is_localized_module.mk' f m s :=
rfl

@[simp]
lemma iso_symm_mk' (m : M) (s : S) :
  (is_localized_module.iso S f).symm (is_localized_module.mk' f m s) = localized_module.mk m s :=
(is_localized_module.iso S f).symm_apply_apply (localized_module.mk m s)

@[simp]
lemma iso_mk' (m : M) (s : S) :
  is_localized_module.iso S f (is_localized_module.mk' (localized_module.mk_linear_map S M) m s) =
    is_localized_module.mk' f m s :=
by rw [← is_localized_module.mk_eq_mk', iso_mk]

local attribute [-simp] iso_symm_apply

@[simp]
lemma lift_mk' (g : M →ₗ[R] M'')
  (h : ∀ (x : S), is_unit ((algebra_map R (module.End R M'')) x)) (m : M) (s : S) :
  (is_localized_module.lift S f g h) (is_localized_module.mk' f m s) = (h s).unit⁻¹ (g m) :=
by { delta is_localized_module.lift, dsimp,
  rw [is_localized_module.iso_symm_mk', localized_module.lift_mk], refl }

end is_localized_module

section submodule

universes u v
variables {R : Type*} [comm_ring R] (S : submonoid R)
variables {M M' M'' : Type*} [add_comm_monoid M] [add_comm_monoid M'] [add_comm_monoid M'']
variables [module R M] [module R M'] [module R M''] (f : M →ₗ[R] M') (g : M →ₗ[R] M'')

variable [is_localized_module S f]

variable (N : submodule R M)

/-- The localization of a submodule of `M` in `localized_module S M`. -/
def submodule.localize : submodule (localization S) (localized_module S M) :=
{ carrier := { x | ∃ (y ∈ N) s, localized_module.mk y s = x },
  add_mem' := begin
    rintros _ _ ⟨x, hx, s, rfl⟩ ⟨x', hx', s', rfl⟩,
    refine ⟨_, _, _, localized_module.mk_add_mk⟩,
    apply add_mem; apply submodule.smul_mem; assumption
  end,
  zero_mem' := ⟨_, zero_mem _, _, rfl⟩,
  smul_mem' := begin
    rintros r _ ⟨x, hx, s, rfl⟩,
    induction r using localization.induction_on,
    exact ⟨_, N.smul_mem _ hx, _, rfl⟩,
  end }

variables {S N}

lemma submodule.mem_localize_of_mem {x : M} (hx : x ∈ N) (s : S) :
  localized_module.mk x s ∈ N.localize S :=
⟨_, hx, _, rfl⟩

variables (S N)

lemma submodule.localize_eq_span :
  N.localize S = submodule.span (localization S) (N.map $ localized_module.mk_linear_map S M) :=
begin
  apply le_antisymm,
  { rintro _ ⟨x, hx, s, rfl⟩,
    rw [← mul_one s, ← one_smul R x, ← localized_module.mk_smul_mk],
    exact submodule.smul_mem _ (localization.mk (1 : R) s)
      (submodule.subset_span $ submodule.mem_map_of_mem hx) },
  { rw submodule.span_le,
    rintros _ ⟨x, hx, rfl⟩,
    exact submodule.mem_localize_of_mem hx _ }
end

lemma submodule.localize_span (s : set M) :
  (submodule.span R s).localize S =
    submodule.span (localization S) (localized_module.mk_linear_map S M '' s) :=
by rw [submodule.localize_eq_span, submodule.map_span, submodule.span_span_of_tower]

@[simp]
lemma submodule.localize_bot : (⊥ : submodule R M).localize S = ⊥ :=
by rw [← submodule.span_empty, submodule.localize_span, set.image_empty, submodule.span_empty]

@[simp]
lemma submodule.localize_top : (⊤ : submodule R M).localize S = ⊤ :=
begin
  rw eq_top_iff,
  rintros x -,
  induction x using localized_module.induction_on,
  exact submodule.mem_localize_of_mem trivial _
end

end submodule

section base_change

variables {R : Type*} [comm_ring R] (S : submonoid R)
variables {M M' M'' : Type*} [add_comm_monoid M] [add_comm_monoid M'] [add_comm_monoid M'']
variables [module R M] [module R M'] [module R M''] (f : M →ₗ[R] M') (g : M →ₗ[R] M'')
variables (R' : Type*) [comm_ring R'] [algebra R R'] [is_localization S R']
variables [module R' M'] [is_scalar_tower R R' M'] [module R' M''] [is_scalar_tower R R' M'']


/-- If `M''` is an `S⁻¹R` module, then any `M →ₗ[R] M''` can be lifted to `S⁻¹M →ₗ[S⁻¹R] M''`. -/
noncomputable
def is_localized_module.base_change [is_localized_module S f] (g : M →ₗ[R] M'') : M' →ₗ[R'] M'' :=
begin
  have : ∀ (x : S), is_unit (algebra_map R (module.End R M'') ↑x),
  { intro x,
    have := (is_localization.map_units R' x).map (algebra_map R' (module.End R' M'')),
    rw module.End_is_unit_iff at this ⊢,
    convert this using 1,
    ext n,
    exact (algebra_map_smul _ _ _).symm },
  refine { map_smul' := _, ..is_localized_module.lift S f g this },
  { intros r x,
    obtain ⟨⟨r', s⟩, e⟩ := is_localization.surj S r,
    obtain ⟨⟨x, t⟩, rfl⟩ := is_localized_module.mk'_surjective S f x,
    simp_rw module.End_is_unit_iff at this,
    apply (this s).injective,
    dsimp at e ⊢,
    rw [mul_comm, ← algebra.smul_def] at e,
    rw [← smul_assoc, e, algebra_map_smul, ← linear_map.map_smul, ← linear_map.map_smul,
      ← smul_assoc, e, algebra_map_smul] }
end

lemma _root_.is_localization.smul_mk' (r s : R) (m : S) :
  r • is_localization.mk' R' s m = is_localization.mk' R' (r * s) m :=
by rw [algebra.smul_def, is_localization.mul_mk'_eq_mk'_of_mul]


@[simp]
lemma is_localized_module.base_change_mk' [is_localized_module S f] (g : M →ₗ[R] M'') (m) (s : S) :
    is_localized_module.base_change S f R' g (is_localized_module.mk' f m s) =
      (is_localization.mk' R' 1 s) • (g m) :=
begin
  dsimp [is_localized_module.base_change],
  rw [is_localized_module.lift_mk', module.End_algebra_map_is_unit_inv_apply_eq_iff,
    ← smul_assoc, is_localization.smul_mk', is_localization.mk'_mul_cancel_left, map_one, one_smul],
end

variable (M'')

/-- `is_localized_module.base_change` as an `R`-linear map. -/
@[simps]
noncomputable
def is_localized_module.base_change_linear_map [is_localized_module S f] :
  (M →ₗ[R] M'') →ₗ[R] M' →ₗ[R'] M'' :=
{ to_fun := is_localized_module.base_change S f R',
  map_add' := begin
    intros g₁ g₂,
    ext x,
    obtain ⟨⟨x, t⟩, rfl⟩ := is_localized_module.mk'_surjective S f x,
    dsimp,
    simp only [is_localized_module.base_change_mk', linear_map.add_apply, smul_add],
  end,
  map_smul' := begin
    intros r g,
    ext x,
    obtain ⟨⟨x, t⟩, rfl⟩ := is_localized_module.mk'_surjective S f x,
    dsimp,
    simp only [is_localized_module.base_change_mk', linear_map.smul_apply],
    rw smul_comm,
  end }
.

local notation `S⁻¹R` := localization S
local notation `S⁻¹` := localized_module S

/-- `S⁻¹M →ₗ[S⁻¹R] S⁻¹M'`, the localization of a linear_map `M →ₗ[R] M'`. -/
noncomputable
def localized_module.map :
  (M →ₗ[R] M') →ₗ[R] S⁻¹ M →ₗ[S⁻¹R] S⁻¹ M' :=
  ((is_localized_module.base_change_linear_map S (S⁻¹ M')
    (localized_module.mk_linear_map S M) S⁻¹R).comp (linear_map.comp_right $
      localized_module.mk_linear_map S M'))

alias is_localized_module.mk_eq_mk' ← localized_module.mk_eq_mk'

@[simp]
lemma localized_module.map_mk (x : M) (m : S) :
  localized_module.map S f (localized_module.mk x m) =
    localized_module.mk (f x) m :=
begin
  dsimp [localized_module.map],
  rw [localized_module.mk_eq_mk', is_localized_module.base_change_mk'],
  dsimp,
  rw [ ← localization.mk_eq_mk', localized_module.mk_smul_mk, one_smul, mul_one],
end

@[simp]
lemma localized_module.map_id :
  localized_module.map S (linear_map.id : M →ₗ[R] M) = linear_map.id :=
begin
  apply linear_map.ext,
  intro x,
  induction x using localized_module.induction_on,
  exact localized_module.map_mk _ _ _ _
end

@[simp]
lemma localized_module.map_comp (g : M' →ₗ[R] M'') :
  localized_module.map S (g.comp f) =
    (localized_module.map S g).comp (localized_module.map S f) :=
begin
  apply linear_map.ext,
  intro x,
  induction x using localized_module.induction_on,
  simp,
end

lemma submodule.localize_comap_map {N' : submodule R M'} :
  (N'.localize S).comap (localized_module.map S f) = (N'.comap f).localize S :=
begin
  apply le_antisymm,
  { rintros x ⟨x', hx, r, e⟩,
    induction x using localized_module.induction_on with x s,
    simp_rw [localized_module.map_mk, localized_module.mk_eq, submonoid.smul_def, ← f.map_smul,
      smul_smul] at e,
    obtain ⟨u, e⟩ := e,
    refine ⟨(u * r : R) • x, _, u * r * s, _⟩,
    { dsimp, rw e, exact N'.smul_mem _ hx },
    { rw [← submonoid.coe_mul, ← submonoid.smul_def],
      exact localized_module.mk_cancel_common_left _ _ _ } },
  { rintros _ ⟨x, hx, s, rfl⟩, dsimp, rw localized_module.map_mk,
    exact submodule.mem_localize_of_mem hx _ }
end

lemma submodule.localize_map_map {N : submodule R M} :
  (N.localize S).map (localized_module.map S f) = (N.map f).localize S :=
begin
  apply le_antisymm,
  { rintros _ ⟨_, ⟨x, hx, s, rfl⟩, rfl⟩,
    rw [localized_module.map_mk],
    exact submodule.mem_localize_of_mem (submodule.mem_map_of_mem hx) _ },
  { rintros _ ⟨_, ⟨x, hx, rfl⟩, s, rfl⟩, rw ← localized_module.map_mk,
    exact submodule.mem_map_of_mem (submodule.mem_localize_of_mem hx _) }
end

end base_change

