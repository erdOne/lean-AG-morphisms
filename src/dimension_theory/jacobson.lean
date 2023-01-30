import ring_theory.finite_type
import ring_theory.jacobson
import algebraic_geometry.prime_spectrum.basic
import for_mathlib.jacobson_space

open ideal

lemma is_jacobson_of_finite_type (A B : Type*) [comm_ring A] [comm_ring B]
  [algebra A B] [is_jacobson A] [H : algebra.finite_type A B] : is_jacobson B :=
begin
  obtain ⟨ι, hι, f, hf⟩ := algebra.finite_type.iff_quotient_mv_polynomial'.mp H,
  exactI ideal.is_jacobson_of_surjective ⟨f.to_ring_hom, hf⟩
end

lemma is_jacobson_of_ring_hom_finite_type {A B : Type*} [comm_ring A] [comm_ring B]
  (f : A →+* B) [is_jacobson A] (H : f.finite_type) : is_jacobson B :=
@@is_jacobson_of_finite_type A B _ _ f.to_algebra _ H

-- move me
lemma finite_of_finite_type_of_is_integral
  (R S : Type*) [comm_ring R] [field S] [is_jacobson R] [algebra R S]
  [h₁ : algebra.finite_type R S] [h₂ : algebra.is_integral R S] :
  module.finite R S :=
begin
  convert h₂.to_finite _,
  { apply algebra.algebra_ext, intro r, refl },
  delta ring_hom.finite_type,
  convert h₁,
  apply algebra.algebra_ext, intro r, refl 
end

lemma finite_of_finite_type_of_is_jacobson_of_field 
  (R S : Type*) [comm_ring R] [field S] [is_jacobson R] [algebra R S]
  [H : algebra.finite_type R S] :
  module.finite R S :=
begin
  obtain ⟨ι, hι, f, hf⟩ := algebra.finite_type.iff_quotient_mv_polynomial'.mp H,
  haveI : algebra.is_integral R S,
  { delta algebra.is_integral,
    rw ← f.comp_algebra_map, 
    exactI mv_polynomial.comp_C_integral_of_surjective_of_jacobson f hf },
  exact @@finite_of_finite_type_of_is_integral R S _ _ _ _ _ ‹_›,
  -- why does instance search not work above?
end

lemma prime_spectrum.is_jacobson_of_is_jacobson (R : Type*) [comm_ring R] [is_jacobson R] :
  topological_space.is_jacobson (prime_spectrum R) :=
begin
  rw topological_space.is_jacobson_iff_locally_closed,
  intros S hS hS',
  obtain ⟨U, Z, hU, hZ, rfl⟩ := is_locally_closed_iff.mp hS',
  simp only [← is_closed_compl_iff, prime_spectrum.is_closed_iff_zero_locus_ideal,
    @compl_eq_comm _ U] at hU hZ,
  obtain ⟨⟨I, rfl⟩, ⟨J, rfl⟩⟩ := ⟨hU, hZ⟩,
  simp only [← set.ne_empty_iff_nonempty, ne.def, set.inter_assoc,
    ← set.disjoint_iff_inter_eq_empty, set.disjoint_compl_left_iff_subset,
    prime_spectrum.zero_locus_subset_zero_locus_iff, ideal.radical_eq_jacobson,
    ideal.jacobson, le_Inf_iff] at hS ⊢,
  contrapose! hS,
  rintros x ⟨hJx, hx⟩,
  exact @hS ⟨x, hx.is_prime⟩ ⟨hJx, (prime_spectrum.is_closed_singleton_iff_is_maximal _).mpr hx⟩
end

lemma ideal.is_radical_jacobson {R : Type*} [comm_ring R] (I : ideal R) : I.jacobson.is_radical :=
is_radical_of_eq_jacobson jacobson_idem

lemma prime_spectrum.is_jacobson_iff_is_jacobson {R : Type*} [comm_ring R] :
  is_jacobson R ↔ topological_space.is_jacobson (prime_spectrum R) :=
begin
  refine ⟨@@prime_spectrum.is_jacobson_of_is_jacobson R _, λ H, ⟨λ I hI, le_antisymm _ le_jacobson⟩⟩,
  rw ← I.is_radical_jacobson.radical, conv_rhs { rw ← hI.radical },
  simp_rw [← prime_spectrum.vanishing_ideal_zero_locus_eq_radical],
  apply prime_spectrum.vanishing_ideal_anti_mono,
  rw [← H _ (prime_spectrum.is_closed_zero_locus I),
    (prime_spectrum.is_closed_zero_locus _).closure_subset_iff],
  rintro x ⟨hx : I ≤ x.as_ideal, hx'⟩,
  show jacobson I ≤ x.as_ideal,
  exact Inf_le ⟨hx, (prime_spectrum.is_closed_singleton_iff_is_maximal _).mp hx'⟩
end