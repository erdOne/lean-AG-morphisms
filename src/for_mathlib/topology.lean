import topology.subset_properties

lemma proper_of_compact_fibers {α β : Type*} [topological_space α] [topological_space β] 
  (f : α → β) (h₁ : ∀ x, is_compact (f ⁻¹' {x})) (h₂ : is_closed_map f)
    {K : set β} (hK : is_compact K) : is_compact (f ⁻¹' K) :=
begin
  classical,
  simp_rw is_compact_iff_finite_subcover at h₁ ⊢ hK,
  intros ι U hU hU',
  have := λ (x : K),
    h₁ x U hU ((set.preimage_mono $ set.singleton_subset_iff.mpr x.2).trans hU'),
  choose ι' hι',
  let V : K → set β := λ x, (f '' (⋃ i ∈ ι' x, U i)ᶜ)ᶜ,
  have hV : ∀ x, is_open (V x),
  { intro x, rw is_open_compl_iff, apply h₂, rw is_closed_compl_iff,
    exact is_open_Union (λ i, is_open_Union $ λ _, hU i) },
  obtain ⟨t, ht⟩ := hK V hV _,
  swap,
  { intros x hx,
    by_contra h,
    simp_rw [set.mem_Union, set.mem_compl_iff] at h,
    push_neg at h, 
    obtain ⟨y, hy, rfl⟩ := h ⟨x, hx⟩,
    exact hy (hι' ⟨_, hx⟩ (set.mem_singleton (f y))) },
  use t.bUnion ι',
  rintro x hx,
  obtain ⟨k, hkt, hkV⟩ := (set.mem_Union₂.mp $ ht hx),
  have : x ∈ ⋃ (i : ι) (H : i ∈ ι' k), U i,
  { contrapose hkV, rw [set.mem_compl_iff, not_not], exact ⟨_, hkV, rfl⟩ },
  obtain ⟨i, hi, hiU⟩ := (set.mem_Union₂.mp this),
  exact set.mem_Union₂_of_mem (finset.mem_bUnion.mpr ⟨k, hkt, hi⟩) hiU
end
