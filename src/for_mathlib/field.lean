import logic.equiv.transfer_instance

lemma ring_hom.is_field {R S : Type*} [field R] [semiring S] [nontrivial S] (f : R →+* S)
  (hf : function.surjective f) : is_field S :=
begin
  constructor,
  { exact exists_pair_ne _ },
  { intros x y, obtain ⟨x, rfl⟩ := hf x, obtain ⟨y, rfl⟩ := hf y,
    rw [← map_mul, ← map_mul, mul_comm] },
  { intros a ha, obtain ⟨a, rfl⟩ := hf a, use f (1 / a), rw [← map_mul, mul_div_cancel', map_one], 
    rintro rfl, apply ha, rw map_zero }
end

lemma ring_equiv.is_field {R S : Type*} [field R] [semiring S] (f : R ≃+* S) : is_field S :=
begin
  haveI := f.to_equiv.symm.nontrivial,
  exact f.to_ring_hom.is_field f.surjective
end
