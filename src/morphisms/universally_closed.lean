/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import morphisms.basic
import algebraic_geometry.fiber
import algebraic_geometry.prime_spectrum_more
import morphisms.quasi_compact
import for_mathlib.topology
import for_mathlib.specializing
import for_mathlib.pi
import ring_theory.ideal.minimal_prime

/-!
# Universally closed morphism

A morphism of schemes `f : X ⟶ Y` is universally closed if `X ×[Y] Y' ⟶ Y'` is a closed map
for all base change `Y' ⟶ Y`.

We show that being universally closed is local at the target, and is stable under compositions and
base changes.

-/

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universes v u

namespace algebraic_geometry

variables {X Y : Scheme.{u}} (f : X ⟶ Y)

open category_theory.morphism_property
open algebraic_geometry.morphism_property (topologically)

/--
A morphism of schemes `f : X ⟶ Y` is universally closed if the base change `X ×[Y] Y' ⟶ Y'`
along any morphism `Y' ⟶ Y` is (topologically) a closed map.
-/
@[mk_iff]
class universally_closed (f : X ⟶ Y) : Prop :=
(out : universally (topologically @is_closed_map) f)

lemma universally_closed_eq :
  @universally_closed = universally (topologically @is_closed_map) :=
begin
  ext X Y f, rw universally_closed_iff
end

lemma universally_closed_respects_iso :
  respects_iso @universally_closed :=
universally_closed_eq.symm ▸ universally_respects_iso (topologically @is_closed_map)

lemma universally_closed_stable_under_base_change :
  stable_under_base_change @universally_closed :=
universally_closed_eq.symm ▸ universally_stable_under_base_change (topologically @is_closed_map)

lemma universally_closed_stable_under_composition :
  stable_under_composition @universally_closed :=
begin
  rw universally_closed_eq,
  exact stable_under_composition.universally (λ X Y Z f g hf hg, is_closed_map.comp hg hf),
end

instance universally_closed_type_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [hf : universally_closed f] [hg : universally_closed g] :
  universally_closed (f ≫ g) :=
universally_closed_stable_under_composition f g hf hg

instance universally_closed_fst {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z)
  [hg : universally_closed g] :
  universally_closed (pullback.fst : pullback f g ⟶ _) :=
universally_closed_stable_under_base_change.fst f g hg

instance universally_closed_snd {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z)
  [hf : universally_closed f] :
  universally_closed (pullback.snd : pullback f g ⟶ _) :=
universally_closed_stable_under_base_change.snd f g hf

lemma morphism_restrict_base {X Y : Scheme} (f : X ⟶ Y) (U : opens Y.carrier) :
  ⇑(f ∣_ U).1.base = U.1.restrict_preimage f.1 :=
funext (λ x, subtype.ext $ morphism_restrict_base_coe f U x)

lemma universally_closed_is_local_at_target :
  property_is_local_at_target @universally_closed :=
begin
  rw universally_closed_eq,
  apply universally_is_local_at_target_of_morphism_restrict,
  { exact stable_under_composition.respects_iso (λ X Y Z f g hf hg, is_closed_map.comp hg hf)
      (λ X Y f, (Top.homeo_of_iso (Scheme.forget_to_Top.map_iso f)).is_closed_map) },
  { intros X Y f ι U hU H,
    simp_rw [topologically, morphism_restrict_base] at H,
    exact (is_closed_map_iff_is_closed_map_of_supr_eq_top hU).mpr H }
end

lemma universally_closed.open_cover_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
  (𝒰 : Scheme.open_cover.{u} Y) :
  universally_closed f ↔
    (∀ i, universally_closed (pullback.snd : pullback f (𝒰.map i) ⟶ _)) :=
universally_closed_is_local_at_target.open_cover_iff f 𝒰

lemma universally_closed.is_closed_map (f : X ⟶ Y) [H : universally_closed f] : 
  is_closed_map f.1.base :=
(topologically @is_closed_map).universally_le _ _ _ H.out

lemma universally_closed.compact_space_of_field {R : Type*} [field R] {X : Scheme}
  (f : X ⟶ Scheme.Spec.obj (op $ CommRing.of R)) [H : universally_closed f] :
    compact_space X.carrier :=
begin
  classical,
  unfreezingI { contrapose H },
  rw universally_closed_iff,
  delta morphism_property.universally topologically is_closed_map,
  push_neg,
  let S := Scheme.Spec.obj (op $ CommRing.of R),
  let T := Scheme.Spec.obj (op $ CommRing.of $ mv_polynomial X.affine_opens R),
  let Ti : X.affine_opens → opens T.carrier := λ i, prime_spectrum.basic_open (mv_polynomial.X i),
  let g : T ⟶ S := Scheme.Spec.map (CommRing.of_hom 
    (algebra_map R (mv_polynomial X.affine_opens R) : _)).op,
  let p₁ : pullback g f ⟶ _ := pullback.fst,
  let p₂ : pullback g f ⟶ _ := pullback.snd,
  let XTi : X.affine_opens → Scheme := λ i, pullback
    (T.of_restrict (Ti i).open_embedding ≫ g)
    (X.of_restrict i.1.open_embedding ≫ f),
  let hi : ∀ i, XTi i ⟶ pullback g f :=
    λ i, pullback.map _ _ _ _ _ _ _ (category.comp_id _) (category.comp_id _),
  haveI : unique S.carrier := show unique (prime_spectrum R), by apply_instance,
  let s : S.carrier := (show prime_spectrum R, from ⊥),
  let t : T.carrier := prime_spectrum.comap
    (mv_polynomial.eval $ λ (_ : X.affine_opens), (1 : R)) s,
  let Z := (⨆ i, (hi i).opens_range).compl,
  refine ⟨_, T, _, g, _, is_pullback.of_has_pullback _ _, Z.1, Z.2, λ hZ, _⟩,
  change is_closed (p₁.1.base '' Z.1) at hZ,
  have : t ∉ p₁.1.base '' Z.1,
  { rintro ⟨x, hx, hxt⟩,
    apply hx,
    apply opens.mem_supr.mpr,
    let i : X.affine_opens := ⟨_, range_is_affine_open_of_open_immersion
      (X.affine_cover.map $ p₂.1.base x)⟩,
    have : t ∈ (Ti i).val,
    { rintro ht, dsimp [s] at ht, rw [mv_polynomial.eval_X] at ht, exact one_ne_zero ht },
    refine ⟨i, _⟩,
    change x ∈ set.range _,
    simp only [pullback.range_map, Scheme.of_restrict_val_base, set.mem_inter_iff, opens.inclusion,
      set.mem_preimage, continuous_map.coe_mk, subtype.range_coe_subtype],
    exact ⟨hxt.symm ▸ this, X.affine_cover.covers _⟩ },
  obtain ⟨q : mv_polynomial _ R, hq₁, hq₂⟩ : ∃ q, p₁.1.base '' Z.1 ⊆ prime_spectrum.zero_locus {q} ∧
    t ∉ prime_spectrum.zero_locus ({q} : set (mv_polynomial X.affine_opens R)),
  { by_contra hq, push_neg at hq, apply this,
    obtain ⟨s, hs⟩ := (prime_spectrum.is_closed_iff_zero_locus _).mp hZ,
    simp_rw hs at hq ⊢,
    intros q hq',
    exact hq q (prime_spectrum.zero_locus_anti_mono $ set.singleton_subset_iff.mpr hq') rfl },
  obtain ⟨σq, q', hq'⟩ := q.exists_finset_rename,
  let ϕ := @mv_polynomial.aeval R (mv_polynomial _ R) _ _ _ _
    (λ i : X.affine_opens, if i ∈ σq then mv_polynomial.X i else 0),
  let t' := prime_spectrum.comap ϕ.to_ring_hom t,
  have ϕq : ϕ q = q,
  { rw [hq', mv_polynomial.aeval_rename, mv_polynomial.rename],
    have : ∀ i : σq, ↑i ∈ σq := subtype.prop,
    simp_rw [function.comp, if_pos (this _)] },
  have ht'₁ : t' ∉ prime_spectrum.zero_locus ({q} : set (mv_polynomial X.affine_opens R)),
  { rwa [← @set.mem_preimage _ _ (prime_spectrum.comap ϕ.to_ring_hom),
      prime_spectrum.preimage_comap_zero_locus, set.image_singleton,
      alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom, ϕq] },
  have ht'₂ : ∀ i ∉ σq, t' ∉ Ti i,
  { intros i hi,
    change t' ∉ (prime_spectrum.basic_open (mv_polynomial.X i)).1,
    rw [subtype.val_eq_coe, prime_spectrum.basic_open_eq_zero_locus_compl, set.not_mem_compl_iff,
      ← @set.mem_preimage _ _ (prime_spectrum.comap ϕ.to_ring_hom),
      prime_spectrum.preimage_comap_zero_locus, set.image_singleton,
      alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom, mv_polynomial.aeval_X, if_neg hi,
      prime_spectrum.zero_locus_singleton_zero],
    trivial },
  obtain ⟨x, hx⟩ : ∃ x, x ∉ ⨆ i : σq, i.1.1,
  { have : (⨆ i : σq, i.1.1) ≠ ⊤,
    { intro e, apply H, rw [← is_compact_univ_iff, ← opens.coe_top, ← e, opens.coe_supr],
      apply is_compact_Union, exact λ i, i.1.2.is_compact },
    contrapose! this, rw eq_top_iff, exact λ x _, this x },
  let Tp : pullback.triplet g f := ⟨t', x, default, unique.eq_default _, unique.eq_default _⟩,
  obtain ⟨z, hz : p₁.1.base z = t', rfl : p₂.1.base z = x⟩ := Tp.exists_preimage,
  apply ht'₁,
  apply hq₁,
  refine ⟨_, λ hz', _, hz⟩,
  obtain ⟨i, z', rfl⟩ := opens.mem_supr.mp hz',
  by_cases hi : i ∈ σq,
  { apply hx, refine opens.mem_supr.mpr ⟨⟨i, hi⟩, _⟩,
    rw [← Scheme.comp_val_base_apply, pullback.lift_snd],
    exact ((Scheme.forget_to_Top.map pullback.snd) z').prop },
  { rw [← Scheme.comp_val_base_apply, pullback.lift_fst] at hz,
    apply ht'₂ i hi, rw ← hz,
    exact ((Scheme.forget_to_Top.map pullback.fst) z').prop }
end
.
lemma universally_closed.to_closed_map (f : X ⟶ Y) [universally_closed f] : 
  is_closed_map f.1.base :=
begin
  apply universally_le (topologically @is_closed_map),
  rwa ← universally_closed_eq,
end

lemma universally_closed.is_compact_preimage (f : X ⟶ Y) [H : universally_closed f] 
  {K : set Y.carrier} (hK : is_compact K) : is_compact (f.1.base ⁻¹' K) :=
begin
  refine proper_of_compact_fibers _ (λ x, _) (universally_closed.to_closed_map f) hK,  
  haveI : universally_closed (f.fiber_to_residue_field x),
  { delta Scheme.hom.fiber_to_residue_field, apply_instance },
  have := @universally_closed.compact_space_of_field
    (local_ring.residue_field (Y.presheaf.stalk x)) _ _ (f.fiber_to_residue_field x) _,
  rw [← f.range_fiber_ι x, ← set.image_univ],
  rw [← is_compact_univ_iff] at this,
  exact this.image (by continuity)
end

@[priority 100]
instance universally_closed.to_quasi_compact (f : X ⟶ Y) [universally_closed f] : 
  quasi_compact f :=
⟨λ U hU, universally_closed.is_compact_preimage f⟩

section specializing

-- move me
/-- The coordinate ring of a component in the `affine_cover`. -/
def Scheme.affine_cover_ring (X : Scheme) (i : X.affine_cover.J) : CommRing :=
CommRing.of $ (X.local_affine i).some_spec.some

-- move me
lemma Scheme.affine_cover_obj (X : Scheme) (i : X.affine_cover.J) :
  X.affine_cover.obj i = Scheme.Spec.obj (op $ X.affine_cover_ring i) := rfl

lemma image_is_closed_iff_is_stable_under_specialization_of_affine
  [compact_space X.carrier] {R : CommRing}
  (f : X ⟶ Scheme.Spec.obj (op R)) {Z : set X.carrier} 
  (hZ : is_closed Z) : is_closed (f.1.base '' Z) ↔ stable_under_specialization (f.1.base '' Z) :=
begin
  have : ∀ i, ∃ I : ideal (X.affine_cover_ring i), (X.affine_cover.map i).1.base ⁻¹' Z =
    prime_spectrum.zero_locus (↑I : set (X.affine_cover_ring i)),
  { intro i, apply (prime_spectrum.is_closed_iff_zero_locus_ideal _).mp (is_closed.preimage _ hZ),
    continuity },
  choose I hI,
  let gi : ∀ i : X.affine_cover.J, R ⟶ CommRing.of (X.affine_cover_ring i ⧸ I i) :=
    λ i, (Scheme.Spec.preimage (X.affine_cover.map i ≫ f)).unop ≫ (ideal.quotient.mk _),
  have hgi : ∀ i, Scheme.Spec.map (gi i).op =
    Scheme.Spec.map (quiver.hom.op (ideal.quotient.mk (I i))) ≫ X.affine_cover.map i ≫ f,
  { intro i, simpa only [functor.map_comp, op_comp, quiver.hom.op_unop, functor.image_preimage] },
  let S := Π i : X.affine_cover.finite_subcover.J, X.affine_cover_ring i.1 ⧸ I i.1,
  let g : R →+* S := pi.ring_hom (λ i, gi i.1),
  have : f.1.base '' Z =
    set.range (Scheme.Spec.map (show R ⟶ CommRing.of S, from g).op).1.base,
  { apply le_antisymm,
    { rintro _ ⟨x, hxZ, rfl⟩,
      let i := X.affine_cover.finite_subcover.f x,
      obtain ⟨y, hy : (X.affine_cover.map i.1).1.base y = x⟩ :=
        X.affine_cover.finite_subcover.covers x,
      obtain ⟨y', rfl⟩ : y ∈ set.range (prime_spectrum.comap (ideal.quotient.mk (I i.1))),
      { rw prime_spectrum.range_comap_of_surjective _ _ (ideal.quotient.mk_surjective),
        rwa [ideal.mk_ker, ← hI, set.mem_preimage, hy] },
      let g' : S →+* _ ⧸ I i.1 := pi.eval_ring_hom _ (X.affine_cover.finite_subcover.f x),
      have : g'.comp g = gi i.1 := by { ext, refl },
      refine ⟨prime_spectrum.comap g' y', _⟩,
      rw [← hy, ← Scheme.comp_val_base_apply],
      transitivity (Scheme.Spec.map (gi i.1).op).1.base y',
      { rw ← this, refl }, { rw hgi, refl } },
    { rintros _ ⟨x, rfl⟩,
      obtain ⟨⟨i, x⟩, rfl⟩ := (prime_spectrum.pi_equiv _).symm.surjective x,
      refine ⟨(X.affine_cover.map i.1).val.base
        (prime_spectrum.comap (ideal.quotient.mk _) x), _, _⟩,
      { rw [← set.mem_preimage, hI], intros y hy, change (I i.1)^.quotient.mk y ∈ x.as_ideal,
        rw [ideal.quotient.eq_zero_iff_mem.mpr hy], exact zero_mem _ },
      { let g' : S →+* _ ⧸ I i.1 := pi.eval_ring_hom _ i,
        have : g'.comp g = gi i.1 := by { ext, refl },
        transitivity (Scheme.Spec.map (gi i.1).op).1.base x,
          { rw hgi, refl }, { rw ← this, refl } } } },
  rw this,
  exact prime_spectrum.image_is_closed_iff_is_stable_under_specialization _
end

lemma image_is_closed_iff_is_stable_under_specialization
  (f : X ⟶ Y) [quasi_compact f] {Z : set X.carrier} 
  (hZ : is_closed Z) : is_closed (f.1.base '' Z) ↔ stable_under_specialization (f.1.base '' Z) :=
begin
  refine ⟨is_closed.stable_under_specialization, λ h, _⟩,
  rw is_closed_iff_coe_preimage_of_supr_eq_top Y.affine_cover.supr_opens_range,
  intro i,
  haveI := (quasi_compact_iff_forall_affine f).mp infer_instance _
    (range_is_affine_open_of_open_immersion (Y.affine_cover.map i)),
  haveI := (quasi_compact.affine_open_cover_iff Y.affine_cover f).mp infer_instance i,
  let Z' : set (Y.affine_cover.obj i).carrier := _,
  have : is_closed Z' ↔ stable_under_specialization Z' :=
    image_is_closed_iff_is_stable_under_specialization_of_affine
    (pullback.snd : pullback f (Y.affine_cover.map i) ⟶ _)
    (hZ.preimage (pullback.fst : pullback f (Y.affine_cover.map i) ⟶ _).1.base.2),
  let Z'' : set (Y.affine_cover.map i).opens_range := _, change is_closed Z'',
  let e := homeomorph.of_embedding (Y.affine_cover.map i).1.base 
    PresheafedSpace.is_open_immersion.base_open.to_embedding,
  have hZ : e ⁻¹' Z'' = Z',
  { ext x, simp only [set.mem_preimage, set.mem_image],
    split,
    { rintro ⟨y, hyZ, hxy : f.1.base y = (Y.affine_cover.map i).1.base x⟩,
      let T : pullback.triplet f (Y.affine_cover.map i) := ⟨y, x, _, hxy, rfl⟩,
      obtain ⟨z, hzx : _ = y, hzy⟩ := T.exists_preimage,
      refine ⟨z, _, hzy⟩, rwa ← hzx at hyZ },
    { rintro ⟨x, hx, rfl⟩, refine ⟨_, hx, _⟩, rw [continuous_map.to_fun_eq_coe,
        ← Scheme.comp_val_base_apply, pullback.condition], refl } },
  rw [← e.quotient_map.is_closed_preimage, hZ, this, ← hZ],
  apply stable_under_specialization.preimage,
  apply stable_under_specialization.preimage h,
  all_goals { continuity }
end

lemma quasi_compact.is_closed_map_iff_specializing_map
  (f : X ⟶ Y) [quasi_compact f] : is_closed_map f.1.base ↔ specializing_map f.1.base :=
begin
  refine ⟨is_closed_map.specializing_map, _⟩,
  intros H Z hZ,
  rw image_is_closed_iff_is_stable_under_specialization f hZ,
  exact H.stable_under_specialization_image hZ.stable_under_specialization,
end

lemma universally_closed_eq_quasi_compact_and_universally_specializing : 
  @universally_closed = @quasi_compact ⊓ (topologically @specializing_map).universally :=
begin
  ext X Y f,
  split,
  { introI _, refine ⟨infer_instance, λ X' Y' i₁ i₂ f' h, _⟩,
    haveI := universally_closed_stable_under_base_change h.flip infer_instance,
    exact (quasi_compact.is_closed_map_iff_specializing_map f').mp
      (universally_closed.is_closed_map f') },
  { rintro ⟨h₁, h₂⟩, constructor, introsI X' Y' i₁ i₂ f' h,
    haveI := quasi_compact_stable_under_base_change h.flip infer_instance,
    exact (quasi_compact.is_closed_map_iff_specializing_map f').mpr (h₂ _ _ _ h) }
end

end specializing

end algebraic_geometry
