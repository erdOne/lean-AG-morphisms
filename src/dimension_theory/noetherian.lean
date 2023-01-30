import algebraic_geometry.prime_spectrum.noetherian
import topology.noetherian_space
import ring_theory.ideal.minimal_prime
import ring_theory.ideal.operations

variables {R : Type*} [comm_ring R]

open prime_spectrum topological_space

lemma image_maximals {α β : Type*} {r : α → α → Prop} {s : β → β → Prop} (f : α → β)
  (t : set α)
  (h₁ : ∀ x y ∈ t, r x y ↔ s (f x) (f y))
  (h₂ : t.inj_on f) : f '' maximals r t = maximals s (f '' t) :=
begin
  ext,
  split,
  { rintros ⟨x, hx, rfl⟩,
    refine ⟨⟨_, hx.1, rfl⟩, _⟩,
    rintros _ ⟨y, hy, rfl⟩ e, rw ← h₁ _ hy _ hx.1, exact hx.2 hy ((h₁ _ hx.1 _ hy).mpr e), },
  { rintros ⟨⟨x, hx, rfl⟩, h⟩,
    refine ⟨x, ⟨hx, _⟩, rfl⟩,
    rintros y hy e,
    rw h₁ _ hy _ hx,
    exact (h ⟨y, hy, rfl⟩ ((h₁ _ hx _ hy).mp e)) }
end

lemma zero_locus_minimal_primes :
  zero_locus ∘ coe '' minimal_primes R = irreducible_components (prime_spectrum R) :=
begin
  rw irreducible_components_eq_maximals_closed,
  convert image_maximals (zero_locus ∘ coe) _ _ _ using 2,
  { ext s,
    suffices : is_closed s ∧ is_irreducible s ↔ ∃ (J : ideal R), J.is_prime ∧ zero_locus ↑J = s,
    { simpa },
    split,
    { rintro ⟨h₁, h₂⟩,
      obtain ⟨J, e, rfl⟩ := (is_closed_iff_zero_locus_radical_ideal _).mp h₁,
      rw is_irreducible_zero_locus_iff_of_radical _ e at h₂,
      exact ⟨J, h₂, rfl⟩ },
    { rintros ⟨J, hJ, rfl⟩,
      rw [is_closed_iff_zero_locus_ideal, is_irreducible_zero_locus_iff],
      refine ⟨⟨_, rfl⟩, ideal.is_prime_radical hJ.is_primary⟩ } },
  { rintros J ⟨hJ, -⟩ K ⟨hK, -⟩, dsimp, rw [subset_zero_locus_iff_le_vanishing_ideal,
      vanishing_ideal_zero_locus_eq_radical, hJ.radical] },
  { rintros J ⟨hJ, -⟩ K ⟨hK, -⟩ e, apply_fun vanishing_ideal at e, dsimp at e,
    simp_rw [vanishing_ideal_zero_locus_eq_radical, hJ.radical, hK.radical] at e, exact e }
end

lemma vanishing_ideal_irreducible_components :
  vanishing_ideal '' irreducible_components (prime_spectrum R) = minimal_primes R :=
begin
  rw irreducible_components_eq_maximals_closed,
  change _ = maximals (≥) _,
  convert image_maximals _ _ _ _ using 2,
  { ext p,
    suffices : p.is_prime ↔ ∃ s, (is_closed s ∧ is_irreducible s) ∧ vanishing_ideal s = p,
    { simpa },
    split,
    { rintro hp,
      refine ⟨zero_locus p, ⟨is_closed_zero_locus _, _⟩, _⟩,
      { rwa is_irreducible_zero_locus_iff_of_radical _ hp.is_radical },
      { rw [vanishing_ideal_zero_locus_eq_radical, hp.radical] } },
    { rintros ⟨J, ⟨h₁, h₂⟩, rfl⟩,
      obtain ⟨J, e, rfl⟩ := (is_closed_iff_zero_locus_radical_ideal _).mp h₁,
      rwa [vanishing_ideal_zero_locus_eq_radical, ← is_irreducible_zero_locus_iff] } },
  { rintros J _ K ⟨hK, -⟩, dsimp, rw [← subset_zero_locus_iff_le_vanishing_ideal,
      zero_locus_vanishing_ideal_eq_closure, closure_eq_iff_is_closed.mpr hK] },
  { rintros J ⟨hJ, -⟩ K ⟨hK, -⟩ e, apply_fun zero_locus ∘ (coe : ideal R → set R) at e, dsimp at e,
    simp_rw [zero_locus_vanishing_ideal_eq_closure, closure_eq_iff_is_closed.mpr hK,
      closure_eq_iff_is_closed.mpr hJ] at e, exact e }
end

lemma minimal_primes_finite [is_noetherian_ring R] : (minimal_primes R).finite :=
begin
  rw ← vanishing_ideal_irreducible_components,
  exact noetherian_space.finite_irreducible_components.image _,
end

lemma ideal.minimal_primes_finite [is_noetherian_ring R] (I : ideal R) :
  I.minimal_primes.finite :=
begin
  rw ideal.minimal_primes_eq_comap,
  apply set.finite.image,
  exact minimal_primes_finite
end
