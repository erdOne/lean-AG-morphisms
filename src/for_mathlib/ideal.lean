import ring_theory.ideal.operations

lemma ideal.colon_top {R : Type*} [comm_ring R] (I : ideal R) : 
  I.colon ⊤ = I :=
begin
  suffices : ∀ (x : R), (∀ (p : R), x * p ∈ I) ↔ x ∈ I,
  { simpa [set_like.ext_iff, submodule.mem_colon] },
  exact λ x, ⟨λ h, mul_one x ▸ h 1, λ h y, I.mul_mem_right y h⟩,
end

lemma ideal.quotient.lift_comp {R S : Type*} [comm_ring R] [comm_ring S] 
  (I : ideal R) (f : R →+* S) (H : ∀ (a : R), a ∈ I → f a = 0) :
  (I^.quotient.lift f H).comp I^.quotient.mk = f :=
ring_hom.ext (λ _, rfl)

lemma ideal.map_comp {R A B : Type*} [comm_ring R] [comm_ring A] [comm_ring B]
  (f : R →+* A) (g : A →+* B) (I : ideal R) :
  I.map (g.comp f) = (I.map f).map g :=
begin
  change _ = (ideal.span _).map g,
  rw [ideal.map_span, ← set.image_comp], 
  refl,
end