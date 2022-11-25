import topology.local_at_target

variables {α β : Type*} [topological_space α] [topological_space β] (s t : set α)

def is_locally_closed : Prop := is_open ((coe : closure s → α) ⁻¹' s)

variables {s t}

lemma is_locally_closed_iff_exists_inter_closure : 
  is_locally_closed s ↔ ∃ {U : set α}, is_open U ∧ s = U ∩ (closure s) :=
by simp_rw [is_locally_closed, embedding_subtype_coe.is_open_iff,
    ← (set.image_injective.mpr subtype.coe_injective).eq_iff, set.image_preimage_eq_inter_range,
    subtype.range_coe, set.inter_eq_left_iff_subset.mpr subset_closure, eq_comm]

lemma is_locally_closed_iff : 
  is_locally_closed s ↔ ∃ {U Z : set α}, is_open U ∧ is_closed Z ∧ s = U ∩ Z :=
begin
  rw is_locally_closed_iff_exists_inter_closure,
  split,
  { rintro ⟨U, h₁, h₂⟩, exact ⟨U, _, h₁, is_closed_closure, h₂⟩ },
  { rintro ⟨U, Z, hU, hZ, rfl⟩, refine ⟨U, hU, _⟩,
    apply subset_antisymm,
    { simpa using subset_closure },
    { conv_rhs { rw [← hZ.closure_eq] },
      exact set.inter_subset_inter (refl _) (closure_mono $ set.inter_subset_right _ _) } }
end

lemma is_open.is_locally_closed (hs : is_open s) : is_locally_closed s :=
continuous_subtype_coe.1 _ hs

lemma is_closed.is_locally_closed (hs : is_closed s) : is_locally_closed s :=
begin
  delta is_locally_closed,
  convert is_open_univ,
  rw [hs.closure_eq, set.eq_univ_iff_forall],
  exact λ x, x.2
end

lemma is_locally_closed.inter (hs : is_locally_closed s) (ht : is_locally_closed t) :
  is_locally_closed (s ∩ t) :=
begin
  rw is_locally_closed_iff at hs ht ⊢,
  obtain ⟨U₁, Z₁, hU₁, hZ₁, rfl⟩ := hs,
  obtain ⟨U₂, Z₂, hU₂, hZ₂, rfl⟩ := ht,
  refine ⟨_, _, hU₁.inter hU₂, hZ₁.inter hZ₂, set.inter_inter_inter_comm U₁ Z₁ U₂ Z₂⟩,
end

lemma is_locally_closed.preimage {s : set β} (hs : is_locally_closed s)
  {f : α → β} (hf : continuous f) :
  is_locally_closed (f ⁻¹' s) :=
begin
  rw is_locally_closed_iff at hs ⊢,
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hs,
  exact ⟨_, _, hU.preimage hf, hZ.preimage hf, set.preimage_inter⟩,
end

lemma inducing.is_locally_closed_iff {s : set α}
  {f : α → β} (hf : inducing f) :
  is_locally_closed s ↔ ∃ s' : set β, is_locally_closed s' ∧ f ⁻¹' s' = s :=
begin
  simp_rw [is_locally_closed_iff, hf.is_open_iff, hf.is_closed_iff],
  split,
  { rintros ⟨_, _, ⟨U, hU, rfl⟩, ⟨Z, hZ, rfl⟩, rfl⟩,
    exact ⟨_, ⟨U, Z, hU, hZ, rfl⟩, rfl⟩ },
  { rintros ⟨_, ⟨U, Z, hU, hZ, rfl⟩, rfl⟩,
    exact ⟨_, _, ⟨U, hU, rfl⟩, ⟨Z, hZ, rfl⟩, rfl⟩ },
end

lemma embedding.is_locally_closed_iff {s : set α}
  {f : α → β} (hf : embedding f) :
  is_locally_closed s ↔ ∃ s' : set β, is_locally_closed s' ∧ s' ∩ set.range f = f '' s :=
begin
  simp_rw [hf.to_inducing.is_locally_closed_iff,
    ← (set.image_injective.mpr hf.inj).eq_iff, set.image_preimage_eq_inter_range],
end

lemma is_locally_closed.image {s : set α} (hs : is_locally_closed s)
  {f : α → β} (hf : inducing f) (hf' : is_locally_closed (set.range f)) :
  is_locally_closed (f '' s) :=
begin
  obtain ⟨t, ht, rfl⟩ := hf.is_locally_closed_iff.mp hs,
  rw set.image_preimage_eq_inter_range,
  exact ht.inter hf'
end

lemma is_locally_closed.is_closed_closure_diff (hs : is_locally_closed s) :
  is_closed (closure s \ s) :=
begin
  convert (closed_embedding_subtype_coe is_closed_closure).is_closed_map _ hs.is_closed_compl,
  rw [← set.preimage_compl, set.image_preimage_eq_inter_range, @subtype.range_coe _ (closure s),
    set.diff_eq_compl_inter],
end

def coboundary (s : set α) : set α :=
(closure s \ s)ᶜ

lemma subset_coboundary :
  s ⊆ coboundary s :=
by { rw [coboundary, set.subset_compl_iff_disjoint_right], exact set.disjoint_diff }

lemma coboundary_inter_closure : 
  coboundary s ∩ closure s = s :=
begin
  rw [coboundary, ← set.diff_eq_compl_inter, set.diff_diff_right_self,
    set.inter_eq_right_iff_subset],
  exact subset_closure
end

lemma closure_inter_coboundary : 
  closure s ∩ coboundary s = s :=
by rw [set.inter_comm, coboundary_inter_closure]

lemma is_open_map.coboundary_preimage_subset {f : α → β} (hf : is_open_map f) (s : set β) :
  coboundary (f ⁻¹' s) ⊆ f ⁻¹' (coboundary s) :=
begin
  rw [coboundary, coboundary, set.preimage_compl, set.preimage_diff, set.compl_subset_compl],
  apply set.diff_subset_diff_left,
  exact hf.preimage_closure_subset_closure_preimage
end

lemma continuous.preimage_coboundary_subset {f : α → β} (hf : continuous f) (s : set β) :
  f ⁻¹' (coboundary s) ⊆ coboundary (f ⁻¹' s) :=
begin
  rw [coboundary, coboundary, set.preimage_compl, set.preimage_diff, set.compl_subset_compl],
  apply set.diff_subset_diff_left,
  exact hf.closure_preimage_subset s
end

lemma coboundary_preimage {f : α → β} (hf : is_open_map f) (hf' : continuous f) (s : set β) :
  coboundary (f ⁻¹' s) = f ⁻¹' (coboundary s) :=
(hf.coboundary_preimage_subset s).antisymm (hf'.preimage_coboundary_subset s)

lemma is_locally_closed.is_open_coboundary (hs : is_locally_closed s) :
  is_open (coboundary s) :=
hs.is_closed_closure_diff.is_open_compl

lemma is_locally_closed_iff_is_open_coboundary : 
  is_locally_closed s ↔ is_open (coboundary s) :=
⟨is_locally_closed.is_open_coboundary, λ h, by { rw ← @coboundary_inter_closure _ _ s,
  exact h.is_locally_closed.inter is_closed_closure.is_locally_closed }⟩

lemma is_closed_preimage_coe_coboundary : 
  is_closed ((coe : coboundary s → α) ⁻¹' s) :=
begin
  rw embedding_subtype_coe.to_inducing.is_closed_iff,
  refine ⟨closure s, is_closed_closure, _⟩,
  rw [← (set.image_injective.mpr subtype.coe_injective).eq_iff, set.image_preimage_eq_inter_range,
    set.image_preimage_eq_inter_range, subtype.range_coe, closure_inter_coboundary,
    set.inter_eq_left_iff_subset.mpr subset_coboundary],
end

open topological_space

variables {ι : Type*} {U : ι → opens β} (hU : supr U = ⊤)

include hU

lemma is_locally_closed_iff_coe_preimage_of_supr_eq_top (s : set β) :
  is_locally_closed s ↔ ∀ i, is_locally_closed (coe ⁻¹' s : set (U i)) :=
begin
  simp_rw [is_locally_closed_iff_is_open_coboundary],
  rw is_open_iff_coe_preimage_of_supr_eq_top hU,
  refine forall_congr (λ i, _),
  rw coboundary_preimage (U i).2.open_embedding_subtype_coe.is_open_map
    (U i).2.open_embedding_subtype_coe.continuous,
end
