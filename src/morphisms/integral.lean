/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import morphisms.finite
import morphisms.finite_type
import for_mathlib.integral
import morphisms.universally_closed
import ring_theory.ring_hom.integral
import for_mathlib.algebra_is_pushout

/-!

# Integral morphisms

A morphism of schemes is integral if it is affine and the component of the sheaf map on integral opens
is integral.
We show that this property is local, and is stable under compositions and base-changes.

-/

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universe u

namespace algebraic_geometry

variables {X Y : Scheme.{u}} (f : X ⟶ Y)

/--
A morphism is `integral` if the preimages of integral open sets are integral.
-/
@[mk_iff]
class integral (f : X ⟶ Y) extends affine f : Prop :=
(is_integral_of_affine [] :
  ∀ U : opens Y.carrier, is_affine_open U → (f.1.c.app (op U)).is_integral)

def integral.affine_property : affine_target_morphism_property :=
affine_and (λ R S _ _ f, by exactI ring_hom.is_integral f)

lemma integral_eq_affine_property :
  @integral = target_affine_locally integral.affine_property :=
by { ext, rw [integral_iff, integral.affine_property,
  affine_and_target_affine_locally_iff ring_hom.is_integral_respects_iso] }

lemma integral.affine_property_is_local :
  integral.affine_property.is_local :=
is_local_affine_and _ ring_hom.is_integral_respects_iso ring_hom.localization_is_integral
  ring_hom.is_integral_of_localization_span

lemma integral_is_local_at_target :
  property_is_local_at_target @integral :=
integral_eq_affine_property.symm ▸ integral.affine_property_is_local.target_affine_locally_is_local

lemma integral_respects_iso : morphism_property.respects_iso @integral :=
integral_is_local_at_target.respects_iso

lemma integral_stable_under_composition : morphism_property.stable_under_composition @integral :=
by { rw integral_eq_affine_property, exact affine_and_stable_under_composition _
  ring_hom.is_integral_stable_under_composition }

lemma integral_stable_under_base_change : morphism_property.stable_under_base_change @integral :=
by { rw integral_eq_affine_property, exact affine_and_stable_under_base_change _
  ring_hom.is_integral_respects_iso ring_hom.localization_is_integral
  ring_hom.is_integral_of_localization_span
  ring_hom.is_integral_stable_under_base_change }

lemma integral_le_affine :
  @integral ≤ @affine :=
by { rw integral_eq_affine_property, exact target_affine_locally_affine_and_le_affine _ }

lemma integral_Spec_iff {R S : CommRing} (f : R ⟶ S) :
  integral (Scheme.Spec.map f.op) ↔ ring_hom.is_integral f :=
begin
  rw [integral_eq_affine_property,
    integral.affine_property_is_local.affine_target_iff,
    integral.affine_property, affine_and_Spec_iff ring_hom.is_integral_respects_iso]
end

lemma finite_eq_integral_inf_locally_of_finite_type :
  @finite = @integral ⊓ @locally_of_finite_type :=
begin
  apply property_ext_of_le_affine finite_le_affine
    (inf_le_left.trans integral_le_affine) finite_is_local_at_target
    (integral_is_local_at_target.inf locally_of_finite_type_is_local_at_target),
  intros R S f,
  simp_rw [pi.inf_apply, finite_Spec_iff, integral_Spec_iff, locally_of_finite_type_Spec_iff],
  exact ⟨λ h, ⟨h.to_is_integral, h.to_finite_type⟩,
    λ h, ring_hom.finite.of_is_integral_of_finite_type h.1 h.2⟩
end

instance finite.to_integral [hf : finite f] : integral f :=
by { rw finite_eq_integral_inf_locally_of_finite_type at hf, exact hf.1 }

instance finite.to_locally_of_finite_type [hf : finite f] : locally_of_finite_type f :=
by { rw finite_eq_integral_inf_locally_of_finite_type at hf, exact hf.2 }

-- lemma integral.affine_open_cover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
--   tfae [integral f,
--     ∃ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)],
--       ∀ (i : 𝒰.J), is_affine (pullback f (𝒰.map i)) ∧
--         ring_hom.integral (Scheme.Γ.map (pullback.snd : pullback f (𝒰.map i) ⟶ _).op),
--     ∀ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)] (i : 𝒰.J),
--       is_affine (pullback f (𝒰.map i)) ∧
--         ring_hom.integral (Scheme.Γ.map (pullback.snd : pullback f (𝒰.map i) ⟶ _).op),
--     ∀ {U : Scheme} (g : U ⟶ Y) [is_affine U] [is_open_immersion g],
--       is_affine (pullback f g) ∧
--         ring_hom.integral (Scheme.Γ.map (pullback.snd : pullback f g ⟶ _).op)] :=
-- integral_eq_affine_property.symm ▸
--   integral.affine_property_is_local.affine_open_cover_tfae f

-- lemma integral.open_cover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
--   tfae [integral f,
--     ∃ (𝒰 : Scheme.open_cover.{u} Y), ∀ (i : 𝒰.J),
--       integral (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
--     ∀ (𝒰 : Scheme.open_cover.{u} Y) (i : 𝒰.J),
--       integral (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
--     ∀ (U : opens Y.carrier), integral (f ∣_ U),
--     ∀ {U : Scheme} (g : U ⟶ Y) [is_open_immersion g],
--       integral (pullback.snd : pullback f g ⟶ _)] :=
-- affine_eq_affine_property.symm ▸
--   affine_affine_property_is_local.open_cover_tfae f

lemma integral_over_affine_iff [is_affine Y] :
  integral f ↔ is_affine X ∧ ring_hom.is_integral (Scheme.Γ.map f.op) :=
integral_eq_affine_property.symm ▸
  integral.affine_property_is_local.affine_target_iff f

lemma integral.affine_open_cover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.open_cover.{u} Y)
  [∀ i, is_affine (𝒰.obj i)] (f : X ⟶ Y) :
  integral f ↔ ∀ i, is_affine (pullback f (𝒰.map i)) ∧
    ring_hom.is_integral (Scheme.Γ.map (pullback.snd : pullback f (𝒰.map i) ⟶ _).op) :=
integral_eq_affine_property.symm ▸
  integral.affine_property_is_local.affine_open_cover_iff f 𝒰

lemma integral.open_cover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.open_cover.{u} Y)
  [∀ i, is_affine (𝒰.obj i)] (f : X ⟶ Y) :
  integral f ↔ ∀ i, integral (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
integral_eq_affine_property.symm ▸
  integral.affine_property_is_local.target_affine_locally_is_local.open_cover_iff f 𝒰

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [integral g] :
  integral (pullback.fst : pullback f g ⟶ X) :=
integral_stable_under_base_change (is_pullback.of_has_pullback f g).flip infer_instance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [integral f] :
  integral (pullback.snd : pullback f g ⟶ Y) :=
integral_stable_under_base_change (is_pullback.of_has_pullback f g) infer_instance

lemma topologically_is_closed_map_respects_iso :
  (morphism_property.topologically @is_closed_map).respects_iso :=
begin
  apply morphism_property.stable_under_composition.respects_iso,
  { intros X Y Z f g hf hg, exact hg.comp hf },
  { intros X Y e, exact (Top.homeo_of_iso $ Scheme.forget_to_Top.map_iso e).is_closed_map },
end

lemma is_closed_map_of_is_integral_of_is_affine [integral f] [is_affine Y] :
  is_closed_map f.1.base :=
begin
  haveI := is_affine_of_affine f,
  apply (topologically_is_closed_map_respects_iso.arrow_mk_iso_iff
    (Spec_Γ_arrow_iso_of_is_affine f)).mpr,
  apply prime_spectrum.is_closed_map_of_is_integral,
  exact (integral.is_integral_of_affine f _ (top_is_affine_open _) : _),
end

@[priority 100]
instance integral.to_universally_closed [hf : integral f] : universally_closed f :=
begin
  constructor,
  rintros X' Y' i₁ i₂ f' H,
  replace hf := integral_stable_under_base_change H.flip hf, 
  clear_dependent X Y,
  apply (is_closed_map_iff_is_closed_map_of_supr_eq_top Y'.affine_cover.supr_opens_range).mpr,
  introI i, 
  rw [← morphism_restrict_val_base],
  haveI := integral_is_local_at_target.2 f' (Y'.affine_cover.map i).opens_range infer_instance,
  haveI : is_affine _ := range_is_affine_open_of_open_immersion (Y'.affine_cover.map i),
  apply is_closed_map_of_is_integral_of_is_affine
end


open_locale polynomial
local attribute [instance] polynomial.polynomial_algebra_of_algebra

open_locale big_operators

lemma polynomial.reflect_map {R S : Type*} [comm_ring R] [comm_ring S] (p : R[X]) (f : R →+* S) (n : ℕ) :
  (p.map f).reflect n = (p.reflect n).map f :=
begin
  ext i, simp, 
end 

lemma _root_.ring_hom.is_integral_elem_of_is_nilpotent {R S : Type*} [comm_ring R] [comm_ring S]
  (f : R →+* S) {x : S}
  (hx : is_nilpotent x) : f.is_integral_elem x :=
begin
  cases hx with n hx,
  refine ⟨polynomial.monomial n (1 : R), polynomial.leading_coeff_monomial _ _, _⟩,
  rw [polynomial.eval₂_monomial, hx, mul_zero]
end

lemma integral_eq_affine_inf_universally_closed :
  @integral = @affine ⊓ @universally_closed :=
begin
  apply le_antisymm,
  { introsI X Y f hf, exact ⟨infer_instance, infer_instance⟩ },
  { apply property_le_of_le_affine inf_le_left 
      (affine_is_local_at_target.inf universally_closed_is_local_at_target)
      integral_is_local_at_target,
    simp_rw [pi.inf_apply, integral_Spec_iff],
    rintros R S f ⟨-, h₂⟩ a,
    by_cases ha : is_nilpotent a, { exact ring_hom.is_integral_elem_of_is_nilpotent _ ha },
    let p : S[X] := polynomial.monomial 1 a - polynomial.C 1,
    letI := f.to_algebra,
    haveI : universally_closed (Scheme.Spec.map (CommRing.of_hom (algebra_map R S)).op),
    { convert h₂; exact CommRing.of_eq _ },
    have := universally_closed.out _ _ _
      ((algebra.is_pushout.to_is_pushout R S R[X] S[X]).op.map Scheme.Spec) _
      (prime_spectrum.is_closed_zero_locus $ {p}),
    change is_closed (prime_spectrum.comap (algebra_map R[X] S[X]) ''
      prime_spectrum.zero_locus {p}) at this,
    rw [← prime_spectrum.zero_locus_span, ← closure_eq_iff_is_closed,
      prime_spectrum.closure_image_comap_zero_locus, prime_spectrum.zero_locus_span] at this,
    have : (1 : R[X]) ∈ ideal.span {polynomial.X} ⊔ (ideal.span {p}).comap (algebra_map R[X] S[X]),
    { rw [← ideal.eq_top_iff_one, sup_comm, ← prime_spectrum.zero_locus_empty_iff_eq_top,
      prime_spectrum.zero_locus_sup, this, prime_spectrum.zero_locus_span,
      set.eq_empty_iff_forall_not_mem],
      rintros _ ⟨⟨x, hx : _ ⊆ _, rfl⟩, hx' : _ ⊆ _⟩,
      apply x.2.1,
      replace hx' : polynomial.X ∈ x.as_ideal,
      { rw set.singleton_subset_iff at hx', change _ ∈ x.as_ideal at hx',
        rwa [polynomial.polynomial_algebra_of_algebra_algebra_map_apply, polynomial.map_X] at hx' },
      rw set.singleton_subset_iff at hx,
      have : _ - (_ - _) ∈ _ := sub_mem (x.as_ideal.mul_mem_left (polynomial.C a) hx') hx,
      rwa [polynomial.monomial_eq_C_mul_X, pow_one, sub_sub_cancel,
        map_one, ← ideal.eq_top_iff_one] at this },
    rw ideal.mem_span_singleton_sup at this,
    obtain ⟨a, b, hb, e⟩ := this,
    have h : b.coeff 0 = 1,
    { apply_fun (λ p, polynomial.coeff p 0) at e,
      rwa [polynomial.coeff_add, polynomial.coeff_mul_X_zero, polynomial.coeff_one_zero,
      zero_add] at e },
    rw [ideal.mem_comap, polynomial.polynomial_algebra_of_algebra_algebra_map_apply,
      ideal.mem_span_singleton] at hb,
    obtain ⟨q, hq : b.map f = _⟩ := hb,
    refine ⟨b.reverse * polynomial.X ^ (1 + q.nat_degree), _, _⟩,
    { casesI subsingleton_or_nontrivial R with hR, { exact subsingleton.elim _ _ },
      rw [polynomial.monic, polynomial.leading_coeff_mul_X_pow, polynomial.reverse_leading_coeff,
        ← h, polynomial.trailing_coeff],
      congr' 1,
      exact le_zero_iff.mp (polynomial.nat_trailing_degree_le_of_ne_zero $ h.symm ▸ one_ne_zero) },
    { rw [polynomial.eval₂_eq_eval_map, polynomial.reverse, polynomial.map_mul,
        ← polynomial.reflect_map, polynomial.map_pow, polynomial.map_X,
        ← polynomial.rev_at_zero (1 + q.nat_degree), ← polynomial.reflect_monomial,
        ← polynomial.reflect_mul, pow_zero, mul_one, hq, ← add_assoc, polynomial.reflect_mul,
        polynomial.eval_mul, polynomial.reflect_sub, polynomial.reflect_C,
        polynomial.monomial_eq_C_mul_X, polynomial.reflect_C_mul_X_pow, polynomial.eval_sub,
        polynomial.eval_C_mul, polynomial.eval_C_mul, polynomial.eval_pow, polynomial.eval_X,
        polynomial.eval_pow, polynomial.eval_X, polynomial.rev_at_le, add_tsub_cancel_right,
        ← pow_succ, one_mul, sub_self, zero_mul],
      { exact le_add_self },
      { refine (polynomial.nat_degree_add_le _ _).trans (max_le _ _),
        { exact (polynomial.nat_degree_monomial_le _).trans le_add_self },
        { rw [← polynomial.C_neg, polynomial.nat_degree_C], exact zero_le _ } },
      { exact le_refl _ },
      { exact polynomial.nat_degree_map_le _ _ },
      { rw [pow_zero, polynomial.nat_degree_one], exact zero_le _ } } }
end

@[priority 100]
instance universally_closed.to_integral {X Y : Scheme} (f : X ⟶ Y) [H : integral f] :
  universally_closed f :=
by { rw integral_eq_affine_inf_universally_closed at H, exact H.2 }

instance integral_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [integral f] [integral g] : integral (f ≫ g) :=
integral_stable_under_composition _ _ infer_instance infer_instance

end algebraic_geometry