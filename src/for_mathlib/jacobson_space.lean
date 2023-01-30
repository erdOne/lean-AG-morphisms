import for_mathlib.locally_closed

namespace topological_space

variables (α β : Type*) [topological_space α] [topological_space β] (f : α → β)

def closed_points : set α := { x : α | is_closed ({x} : set α) }

lemma mem_closed_points {x} : x ∈ closed_points α ↔ is_closed ({x} : set α) := iff.rfl

def is_jacobson : Prop :=
∀ Z, is_closed Z → closure (Z ∩ closed_points α) = Z

variables {α β f}

lemma is_jacobson_iff_locally_closed : 
  is_jacobson α ↔ ∀ Z : set α, Z.nonempty → is_locally_closed Z → (Z ∩ closed_points α).nonempty :=
begin
  split,
  { simp_rw [is_locally_closed_iff_is_open_coboundary, coboundary, is_open_compl_iff,
      ← set.ne_empty_iff_nonempty],
    intros H Z hZ hZ' e,
    have : Z ⊆ closure Z \ Z,
    { refine subset_closure.trans _,
      nth_rewrite 0 ← H (closure Z) is_closed_closure,
      rw [hZ'.closure_subset_iff, set.subset_diff, set.disjoint_iff, set.inter_assoc,
        set.inter_comm _ Z, e],
      exact ⟨set.inter_subset_left _ _, set.inter_subset_right _ _⟩ },
    rw [set.subset_diff, disjoint_self, set.bot_eq_empty] at this,
    exact hZ this.2 },
  { intros H Z hZ,
    refine subset_antisymm (hZ.closure_subset_iff.mpr $ set.inter_subset_left _ _) _,
    rw [← set.disjoint_compl_left_iff_subset, set.disjoint_iff_inter_eq_empty, 
      ← set.not_nonempty_iff_eq_empty],
    intro H',
    have := H _ H' (is_closed_closure.is_open_compl.is_locally_closed.inter hZ.is_locally_closed),
    rw [← set.ne_empty_iff_nonempty, ne.def, set.inter_assoc,
      ← set.disjoint_iff_inter_eq_empty, set.disjoint_compl_left_iff_subset] at this,
    exact this subset_closure }
end

alias is_jacobson_iff_locally_closed ↔ is_jacobson.nonempty_inter_closed_points _

lemma is_jacobson.is_closed_of_is_locally_closed (hα : is_jacobson α) {x : α}
  (hx : is_locally_closed ({x} : set α)) : is_closed ({x} : set α) :=
begin
  obtain ⟨_, ⟨y, rfl : y = x, rfl⟩, hy'⟩ := hα.nonempty_inter_closed_points _
    (set.singleton_nonempty x) hx,
  exact hy' 
end

lemma preimage_closed_points_subset (hf : embedding f) :
  f ⁻¹' closed_points β ⊆ closed_points α :=
begin
  intros x hx,
  rw mem_closed_points,
  convert continuous_iff_is_closed.mp hf.continuous _ hx,
  rw [← set.image_singleton, set.preimage_image_eq _ hf.inj]
end

lemma closed_embedding.preimage_closed_points (hf : closed_embedding f) :
  f ⁻¹' closed_points β = closed_points α :=
begin
  ext x, simp [mem_closed_points, ← set.image_singleton, hf.closed_iff_image_closed],
end

lemma open_embedding.preimage_closed_points (hf : open_embedding f) (hβ : is_jacobson β) :
  f ⁻¹' closed_points β = closed_points α :=
begin
  apply subset_antisymm (preimage_closed_points_subset hf.to_embedding),
  intros x hx,
  apply hβ.is_closed_of_is_locally_closed,
  rw ← set.image_singleton,
  exact (hx.is_locally_closed.image hf.to_inducing hf.open_range.is_locally_closed)
end

lemma is_jacobson.of_open_embedding (hα : is_jacobson β)
  (hf : open_embedding f) : is_jacobson α :=
begin
  rw is_jacobson_iff_locally_closed,
  rw ← hf.preimage_closed_points hα,
  rw is_jacobson_iff_locally_closed at hα,
  intros Z hZ hZ',
  obtain ⟨_, ⟨x, hx, rfl⟩, hx'⟩ := hα _ (hZ.image f) (hZ'.image hf.to_inducing 
    hf.open_range.is_locally_closed),
  exact ⟨_, hx, hx'⟩
end

lemma is_jacobson.of_closed_embedding (hα : is_jacobson β)
  (hf : closed_embedding f) : is_jacobson α :=
begin
  rw is_jacobson_iff_locally_closed at hα ⊢,
  rw ← hf.preimage_closed_points,
  intros Z hZ hZ',
  obtain ⟨_, ⟨x, hx, rfl⟩, hx'⟩ := hα _ (hZ.image f) (hZ'.image hf.to_inducing 
    hf.closed_range.is_locally_closed),
  exact ⟨_, hx, hx'⟩
end

lemma is_jacobson.discrete_of_finite [finite α] (hα : is_jacobson α) : discrete_topology α :=
begin
  suffices : closed_points α = set.univ,
  { rw ← forall_open_iff_discrete,
    intro s,
    rw [← is_closed_compl_iff, ← set.bUnion_of_singleton sᶜ],
    refine is_closed_bUnion (set.to_finite _) (λ x hx, _),
    rw [← mem_closed_points, this],
    trivial },
  rw [← set.univ_subset_iff, ← hα _ is_closed_univ, set.univ_inter, closure_subset_iff_is_closed,
    ← set.bUnion_of_singleton (closed_points α)],
  exact is_closed_bUnion (set.to_finite _) (λ _, id),
end

lemma {u} is_jacobson_iff_of_supr_eq_top {α : Type u} [topological_space α]
  {ι : Type u} {U : ι → opens α} (hU : supr U = ⊤) :
  is_jacobson α ↔ ∀ i, is_jacobson (U i) :=
begin
  refine ⟨λ h i, h.of_open_embedding (U i).2.open_embedding_subtype_coe, λ H, _⟩,
  rw is_jacobson_iff_locally_closed,
  intros Z hZ hZ',
  have : (⋃ i, (U i : set α)) = set.univ, { rw ← opens.coe_supr, injection hU },
  have : (⋃ i, Z ∩ U i) = Z, { rw [← set.inter_Union, this, set.inter_univ] },
  rw [← this, set.nonempty_Union] at hZ,
  obtain ⟨i, x, hx, hx'⟩ := hZ,
  obtain ⟨y, hy, hy'⟩ := (is_jacobson_iff_locally_closed.mp $ H i) (coe ⁻¹' Z) ⟨⟨x, hx'⟩, hx⟩
    (hZ'.preimage continuous_subtype_coe),
  refine ⟨y, hy, (is_closed_iff_coe_preimage_of_supr_eq_top hU _).mpr $ λ j, _⟩,
  by_cases (y : α) ∈ U j,
  { convert_to is_closed {(⟨y, h⟩ : U j)}, { ext z, exact @subtype.coe_inj _ _ z ⟨y, h⟩ },
    apply (H j).is_closed_of_is_locally_closed,
    convert (hy'.is_locally_closed.image embedding_subtype_coe.to_inducing
      (U i).2.open_embedding_subtype_coe.open_range.is_locally_closed).preimage
      continuous_subtype_coe,
    rw set.image_singleton, ext z, exact (@subtype.coe_inj _ _ z ⟨y, h⟩).symm },
  { convert is_closed_empty, rw set.eq_empty_iff_forall_not_mem, rintros z (hz : ↑z = ↑y),
    rw ← hz at h, exact h z.2 }
end

end topological_space