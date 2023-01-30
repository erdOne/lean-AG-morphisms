import ring_theory.ideal.local_ring

lemma subring.is_unit_iff {K : Type*} [division_ring K] {A : subring K} (x : A) (hx : x ≠ 0) :
  is_unit x ↔ (x : K)⁻¹ ∈ A :=
begin
  split,
  { rintro ⟨⟨x, y, hxy, hyx⟩, rfl⟩,
    convert y.2,
    rw inv_eq_of_mul_eq_one_left,
    exact subtype.ext_iff.mp hyx },
  { intro h, 
    have : (x : K) ≠ 0 := by { contrapose! hx, ext1, exact hx },
    refine ⟨⟨x, ⟨_, h⟩, _, _⟩, rfl⟩; ext; simp [inv_mul_cancel this, mul_inv_cancel this] }
end

lemma is_local_ring_hom_of_surjective {R S : Type*} [comm_ring R] [local_ring R] [comm_ring S]
  [nontrivial S]
  (f : R →+* S) (hf : function.surjective f) : is_local_ring_hom f :=
begin
  haveI := local_ring.of_surjective' _ hf,
  have := ideal.comap_map_of_surjective f hf (local_ring.maximal_ideal R),
  rw [sup_eq_left.mpr _] at this,
  rw [(local_ring.local_hom_tfae f).out 0 3, ← this],
  { refine ideal.comap_mono (local_ring.le_maximal_ideal _),
    intro e, rw e at this, exact (local_ring.maximal_ideal.is_maximal R).ne_top this.symm },
  { apply local_ring.le_maximal_ideal, intro e, apply @one_ne_zero S, rw ← f.map_one,
    change (1 : R) ∈ ideal.comap f ⊥, rw e, trivial }
end

instance is_local_ring_hom_ring_equiv {R S : Type*} [comm_ring R] [local_ring R] [comm_ring S]
  [nontrivial S] (f : R ≃+* S) : is_local_ring_hom (f : R →+* S) :=
begin
  casesI subsingleton_or_nontrivial S,
  { haveI := f.to_equiv.subsingleton, exact ⟨λ _ _, is_unit_of_subsingleton _⟩ },
  { exact is_local_ring_hom_of_surjective _ f.surjective }
end

lemma local_ring.map_maximal_ideal_of_surjective {R S : Type*} [comm_ring R] [comm_ring S] 
  [local_ring R] [local_ring S] (f : R →+* S) (hf : function.surjective f) : 
  (local_ring.maximal_ideal R).map f = local_ring.maximal_ideal S :=
begin
  nontriviality S,
  haveI := is_local_ring_hom_of_surjective f hf,
  refine le_antisymm (((local_ring.local_hom_tfae f).out 0 2).mp infer_instance) _,
  rw ← ideal.map_comap_of_surjective f hf (local_ring.maximal_ideal S),
  apply ideal.map_mono,
  rw ((local_ring.local_hom_tfae f).out 0 4).mp infer_instance,
  exact le_refl _
end