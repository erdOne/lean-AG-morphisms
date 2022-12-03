import algebraic_geometry.prime_spectrum.basic
import ring_theory.ideal.minimal_prime
import for_mathlib.specializing


namespace prime_spectrum
variables {R S : Type*} [comm_ring R] [comm_ring S] (f : R →+* S) 

lemma image_is_closed_iff_is_stable_under_specialization : 
  is_closed (set.range $ prime_spectrum.comap f) ↔
    stable_under_specialization (set.range $ prime_spectrum.comap f) :=
begin
  refine ⟨is_closed.stable_under_specialization, λ h, _⟩,
  rw prime_spectrum.is_closed_iff_zero_locus_ideal,
  refine ⟨f.ker, _⟩,
  apply le_antisymm,
  { rintro _ ⟨p, rfl⟩ x (hx : f x = 0), show f x ∈ p.1, rw hx, exact zero_mem _ },
  rintros p (hp : f.ker ≤ p.as_ideal),
  obtain ⟨q, hq₁, hq₂⟩ := ideal.exists_minimal_primes_le hp,
  obtain ⟨p', hp', hp'', rfl⟩ := ideal.exists_comap_eq_of_mem_minimal_primes f _ hq₁,
  let p'' : prime_spectrum S := ⟨p', hp'⟩,
  change prime_spectrum.comap f p'' ≤ p at hq₂,
  apply h ((prime_spectrum.le_iff_specializes _ _).mp hq₂),
  exact set.mem_range_self _  
end

lemma closure_image_comap_zero_locus (I : ideal S) :
  closure (prime_spectrum.comap f '' prime_spectrum.zero_locus I) =
    prime_spectrum.zero_locus (I.comap f) :=
begin
  apply subset_antisymm,
  { rw [is_closed.closure_subset_iff, set.image_subset_iff,
      prime_spectrum.preimage_comap_zero_locus],
    exacts [prime_spectrum.zero_locus_anti_mono (set.image_preimage_subset _ _), 
      prime_spectrum.is_closed_zero_locus _] },
  { rintro x (hx : I.comap f ≤ x.as_ideal),
    obtain ⟨q, hq₁, hq₂⟩ := ideal.exists_minimal_primes_le hx,
    obtain ⟨p', hp', hp'', rfl⟩ := ideal.exists_comap_eq_of_mem_minimal_primes f _ hq₁,
    let p'' : prime_spectrum S := ⟨p', hp'⟩,
    apply is_closed_closure.stable_under_specialization
      ((prime_spectrum.le_iff_specializes (prime_spectrum.comap f p'') x).mp hq₂),
    apply subset_closure,
    exact ⟨p'', hp'', rfl⟩ },
end

lemma _root_.ideal.quotient.ker_mk {R : Type*} [comm_ring R] (I : ideal R) :
  I^.quotient.mk^.ker = I := 
by { ext1, exact submodule.quotient.mk_eq_zero _ }

lemma is_closed_map_of_is_integral (H : f.is_integral) :
  is_closed_map (prime_spectrum.comap f) :=
begin
  intros S hS,
  obtain ⟨I, rfl⟩ := (prime_spectrum.is_closed_iff_zero_locus_ideal _).mp hS,
  rw [← I^.quotient.ker_mk, ← prime_spectrum.range_comap_of_surjective _ _
    ideal.quotient.mk_surjective, ← set.range_comp, ← continuous_map.coe_comp,
    ← prime_spectrum.comap_comp, prime_spectrum.image_is_closed_iff_is_stable_under_specialization],
  rintros _ q h ⟨p, rfl⟩,
  rw ← prime_spectrum.le_iff_specializes at h,
  let f' := (ideal.quotient.mk I).comp f,
  have : f'.is_integral := ring_hom.is_integral_trans _ _ H
    (ring_hom.is_integral_of_surjective _ ideal.quotient.mk_surjective),
  letI := f'.to_algebra,
  obtain ⟨q', h₁, h₂, e⟩ :=
    ideal.exists_ideal_over_prime_of_is_integral this q.as_ideal p.as_ideal h,
  exact ⟨⟨q', h₂⟩, prime_spectrum.ext.mpr e⟩
end

lemma surjective_of_is_integral_of_injective (H : f.is_integral) (H' : function.injective f) :
  function.surjective (prime_spectrum.comap f) :=
begin
  rw [← set.range_iff_surjective, ← (is_closed_map_of_is_integral f H).closed_range.closure_eq,
    ← set.image_univ, ← zero_locus_bot, closure_image_comap_zero_locus,
    ← ring_hom.ker_eq_comap_bot, f.injective_iff_ker_eq_bot.mp H', zero_locus_bot]
end

end prime_spectrum