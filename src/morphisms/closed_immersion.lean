/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import morphisms.ring_hom_properties
import morphisms.monomorphism
import topology.sheaves.locally_surjective
import topology.local_at_target
import ring_theory.ring_hom.surjective
import algebraic_geometry.stalk_inducing
import for_mathlib.module_local_property
import algebraic_geometry.pushforward_stalk

/-!

# Closed immersions

A morphism of schemes is a closed immersion if the underlying map is a closed embedding, and 
the sheaf map is locally surjective.

-/

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universe u

namespace algebraic_geometry

variables {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism is a `is_closed_immersion` if the preimages of affine open sets are affine. -/
@[mk_iff]
class is_closed_immersion (f : X ⟶ Y) : Prop :=
(base_closed [] : closed_embedding f.1.base)
(c_locally_surjective [] : Top.presheaf.is_locally_surjective f.1.c)

lemma _root_.Top.presheaf.stalk_pushforward_subsingleton
  {X Y : Top} (F : X.presheaf CommRing) (hF : F.is_sheaf) (f : X ⟶ Y) (x : Y)
    (hx : x ∉ closure (set.range f)) :
  subsingleton ((f _* F).stalk x) :=
begin
  apply subsingleton_of_forall_eq (0 : (f _* F).stalk x),
  intro s,
  obtain ⟨U, hxU, s', e⟩ := (f _* F).germ_exist _ s,
  let V : opens Y := U ⊓ ⟨(closure (set.range f))ᶜ, is_closed_closure.is_open_compl⟩,
  let t : (f _* F).obj (op V) := (f _* F).map (hom_of_le inf_le_left).op s',
  have hxV : x ∈ V := ⟨hxU, hx⟩,
  obtain rfl : (f _* F).germ ⟨x, hxV⟩ t = s,
  { rw [Top.presheaf.germ_res_apply, ← e], refl },
  haveI : subsingleton ((f _* F).obj (op V)),
  { change subsingleton (F.obj $ op $ (opens.map f).obj V),
    refine CommRing.subsingleton_of_is_terminal
      (Top.sheaf.is_terminal_of_eq_empty ⟨F, hF⟩ $ eq_bot_iff.mpr _),
    exact λ x hx, hx.2 (subset_closure ⟨x, rfl⟩) },
  rw [subsingleton.elim t 0, map_zero]
end

lemma is_closed_immersion_iff_stalk {f : X ⟶ Y} :
  is_closed_immersion f ↔
    closed_embedding f.1.base ∧ ∀ x, function.surjective (PresheafedSpace.stalk_map f.1 x) :=
begin
  rw [is_closed_immersion_iff, Top.presheaf.locally_surjective_iff_surjective_on_stalks],
  delta PresheafedSpace.stalk_map,
  split,
  { rintro ⟨h₁, h₂⟩, refine ⟨h₁, λ x, function.surjective.comp _ (h₂ $ f.1.base x)⟩,
    haveI := X.presheaf.stalk_pushforward_iso_of_inducing h₁.to_inducing x,
    exact (as_iso $ X.presheaf.stalk_pushforward CommRing f.1.base x)
      .CommRing_iso_to_ring_equiv.surjective },
  { rintro ⟨h₁, h₂⟩, refine ⟨h₁, λ y, _⟩,
    by_cases y ∈ set.range f.1.base,
    { obtain ⟨x, rfl⟩ := h, 
      haveI := X.presheaf.stalk_pushforward_iso_of_inducing h₁.to_inducing x,
      have := (as_iso $ X.presheaf.stalk_pushforward CommRing f.1.base x).symm
        .CommRing_iso_to_ring_equiv.surjective.comp (h₂ x),
      erw ← coe_comp at this,
      simpa using this },
    { intro s,
      rw ← closure_eq_iff_is_closed.mpr h₁.closed_range at h,
      have := X.presheaf.stalk_pushforward_subsingleton X.sheaf.2 f.1.base y h,
      rw @@subsingleton.elim this s 0,
      exact ⟨0, map_zero _⟩ } }
end

lemma is_closed_immersion.stalk_map_surjective [is_closed_immersion f] (x : X.carrier) :
  function.surjective (PresheafedSpace.stalk_map f.1 x) :=
(is_closed_immersion_iff_stalk.mp infer_instance).2 x

instance is_closed_immersion_of_is_iso (f : X ⟶ Y) [is_iso f] : is_closed_immersion f :=
begin
  refine is_closed_immersion_iff_stalk.mpr ⟨(Top.homeo_of_iso $ as_iso f.1.base).closed_embedding, _⟩,
  intro x,
  exact ((forget _).map_iso (as_iso $ PresheafedSpace.stalk_map f.val x)).to_equiv.surjective,
end

lemma is_closed_immersion_stable_under_composition :
  morphism_property.stable_under_composition @is_closed_immersion :=
begin
  introsI X Y Z f g h₁ h₂,
  rw is_closed_immersion_iff_stalk at h₁ h₂ ⊢,
  refine ⟨h₂.1.comp h₁.1, λ x, _⟩,
  erw PresheafedSpace.stalk_map.comp,
  exact (h₁.2 x).comp (h₂.2 $ f.1 x)
end

lemma is_closed_immersion_respects_iso :
  morphism_property.respects_iso @is_closed_immersion :=
begin
  apply is_closed_immersion_stable_under_composition.respects_iso,
  intros _ _ _, apply_instance
end

lemma is_closed_immersion_is_local_at_target : property_is_local_at_target @is_closed_immersion :=
begin
  constructor,
  { exact is_closed_immersion_respects_iso },
  { simp_rw is_closed_immersion_iff_stalk,
    rintros X Y f U ⟨h₁, h₂⟩,
    split,
    { rw morphism_restrict_val_base, exact h₁.restrict_preimage U.1 },
    { exact λ x, ((morphism_property.surjective_respects_iso _).arrow_iso_iff
      (morphism_restrict_stalk_map f U x)).mpr (h₂ x.1) } },
  { intros X Y f 𝒰 H,
    rw is_closed_immersion_iff_stalk,
    split,
    { apply (closed_embedding_iff_closed_embedding_of_supr_eq_top
        𝒰.supr_opens_range f.1.base.2).mpr,
      intro i,
      have := ((is_closed_immersion_respects_iso.arrow_iso_iff
        (morphism_restrict_opens_range f (𝒰.map i))).mpr (H i)).1,
      rwa [arrow.mk_hom, morphism_restrict_val_base] at this },
    { exact λ x, ((morphism_property.surjective_respects_iso _).arrow_iso_iff
        (morphism_restrict_stalk_map f _ _)).mp ((is_closed_immersion_iff_stalk.mp $
        (is_closed_immersion_respects_iso.arrow_iso_iff (morphism_restrict_opens_range f (𝒰.map _)))
        .mpr (H (𝒰.f $ f.1.base x))).2 ⟨x, 𝒰.covers (f.1.base x)⟩) } }
end

lemma is_affine_of_closed_embedding {X Y : Scheme} (f : X ⟶ Y) [is_affine Y]
  (hf : closed_embedding f.1.base) : is_affine X :=
begin
  have : ∀ x, ∃ (s : Y.presheaf.obj (op ⊤)) (U : X.affine_opens),
    f.1.base x ∈ Y.basic_open s ∧ @Scheme.basic_open X ⊤ (f.1.c.app (op ⊤) s) ≤ U.1,
  { intro x,
    obtain ⟨_, ⟨U, hU : is_affine_open U, rfl⟩, hxU, -⟩ :=
      (is_basis_affine_open X).exists_subset_of_mem_open
      (show x ∈ (set.univ : set X.carrier), from trivial) is_open_univ,
    obtain ⟨V, hV, hV'⟩ := hf.to_inducing.is_open_iff.mp U.prop,
    rw ← hV' at hxU,
    obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hr⟩ :=
      (is_basis_basic_open Y).exists_subset_of_mem_open (show f.1.base x ∈ _, from hxU) hV,
    refine ⟨r, ⟨U, hU⟩, hxr, _⟩,
    rw ← Scheme.preimage_basic_open,
    have := set.preimage_mono hr, rw hV' at this, exact this },
  choose s U hs hU using this,
  have := hf.closed_range,
  obtain ⟨ι, t, ht, ht'⟩ := (is_basis_basic_open Y).open_eq_Union hf.closed_range.1,
  have : ∀ i : ι, ∃ r : Y.presheaf.obj (op ⊤), (Y.basic_open r).1 = t i,
  { intro i, rcases ht' i with ⟨_, ⟨r, rfl⟩, e⟩, exact ⟨r, e⟩ },
  choose t' ht' using this,
  let r : X.carrier ⊕ ι → Y.presheaf.obj (op ⊤) := sum.elim s t',
  apply is_affine_of_span_top_of_is_affine_open X (f.1.c.app (op ⊤) '' set.range r),
  { rw [← ideal.map_span, ← ideal.map_top (f.1.c.app (op ⊤))],
    congr' 1,
    rw [← (top_is_affine_open Y).basic_open_union_eq_self_iff, eq_top_iff],
    rintro x -,
    erw opens.mem_supr,
    by_cases x ∈ set.range f.1.base,
    { obtain ⟨x, rfl⟩ := h, exact ⟨⟨_, sum.inl _, rfl⟩, hs _⟩ },
    { rw [← set.mem_compl_iff, ht, set.mem_Union] at h,
      obtain ⟨i, hi⟩ := h, rw ← ht' at hi, exact ⟨⟨_, sum.inr _, rfl⟩, hi⟩ } },
  { rintro ⟨_, _, ⟨i|i, rfl⟩, rfl⟩; dsimp only [r, sum.elim],
      have := inf_eq_right.mpr (hU i),
      { convert (U i).2.basic_open_is_affine
          (X.presheaf.map (hom_of_le le_top).op $ (f.val.c.app (op ⊤)) (s i)) using 1,
        rw Scheme.basic_open_res,
        exact (inf_eq_right.mpr (hU i)).symm },
      { convert bot_is_affine_open X,
        rw ← Scheme.preimage_basic_open,
        ext1,
        refine @set.preimage_eq_empty _ _ f.1.base _ _,
        apply set.subset_compl_iff_disjoint_right.mp,
        rw [ht', ht],
        exact set.subset_Union _ _ } }
end

lemma is_closed_immersion_le_affine : 
  @is_closed_immersion ≤ @affine :=
begin
  rw [← is_closed_immersion_is_local_at_target.target_affine_locally_eq, affine_eq_affine_property],
  refine target_affine_locally_mono _,
  introsI X Y f H hf,
  exact is_affine_of_closed_embedding f hf.1,
end

instance is_closed_immersion.to_affine [H : is_closed_immersion f] : affine f :=
is_closed_immersion_le_affine X Y f H

lemma surjective_of_is_closed_immersion {R S : CommRing} (f : R ⟶ S)
  [is_closed_immersion (Scheme.Spec.map f.op)] : function.surjective f :=
begin
  letI := f.to_algebra,
  change function.surjective (algebra.of_id R S).to_linear_map,
  apply linear_map.surjective_of_localization_maximal,
  introsI m hm,
  convert_to function.surjective ((localized_module.map m.prime_compl
      (algebra.of_id R S).to_linear_map).restrict_scalars R),
  rw Spec.localized_module_map_iso_stalk_map' R S ⟨m, _⟩,
  apply function.surjective.comp,
  { exact (linear_equiv.to_equiv _).surjective },
  dsimp only,
  apply function.surjective.comp,
  { exact (Top.presheaf.locally_surjective_iff_surjective_on_stalks _).mp
      (is_closed_immersion.c_locally_surjective (Scheme.Spec.map f.op) : _) ⟨m, _⟩ },
  { exact (linear_equiv.to_equiv _).surjective },
end

lemma property_le_of_le_affine {P₁ P₂ : morphism_property Scheme}
  (h₁ : P₁ ≤ @affine)
  (h₁' : property_is_local_at_target P₁) (h₂' : property_is_local_at_target P₂) 
  (h : ∀ {R S : CommRing} (f : R ⟶ S), P₁ (Scheme.Spec.map f.op) → P₂ (Scheme.Spec.map f.op)) :
  P₁ ≤ P₂ :=
begin
  rw [← h₁'.target_affine_locally_eq, ← h₂'.target_affine_locally_eq],
  apply target_affine_locally_mono,
  intros X Y f hX hf,
  haveI := h₁ _ _ _ hf,
  haveI := is_affine_of_affine f,
  have := Γ_Spec.adjunction.unit_naturality f,
  rw [← h₂'.respects_iso.cancel_right_is_iso f (Γ_Spec.adjunction.unit.app Y),
    ← Γ_Spec.adjunction.unit_naturality f, h₂'.respects_iso.cancel_left_is_iso],
  rw [← h₁'.respects_iso.cancel_right_is_iso f (Γ_Spec.adjunction.unit.app Y),
    ← Γ_Spec.adjunction.unit_naturality f, h₁'.respects_iso.cancel_left_is_iso] at hf,
  exact h (Scheme.Γ.map f.op) hf
end

lemma property_ext_of_le_affine {P₁ P₂ : morphism_property Scheme}
  (h₁ : P₁ ≤ @affine) (h₂ : P₂ ≤ @affine)
  (h₁' : property_is_local_at_target P₁) (h₂' : property_is_local_at_target P₂) 
  (h : ∀ {R S : CommRing} (f : R ⟶ S), P₁ (Scheme.Spec.map f.op) ↔ P₂ (Scheme.Spec.map f.op)) :
  P₁ = P₂ :=
begin
  refine (property_le_of_le_affine h₁ h₁' h₂' _).antisymm (property_le_of_le_affine h₂ h₂' h₁' _);
    simp only [h, forall_3_true_iff, imp_self]
end

def is_closed_immersion.affine_property : affine_target_morphism_property :=
affine_and $ λ R S _ _ f, function.surjective f

-- move me
lemma _root_.ring_hom.localization_surjective : 
  ring_hom.localization_preserves (λ R S _ _ f, function.surjective ⇑f) :=
begin
  introsI R S _ _ f M R' S' _ _ _ _ _ _ H x,
  obtain ⟨x, ⟨_, ⟨s, hs, rfl⟩⟩, rfl⟩ := is_localization.mk'_surjective (M.map f) x,
  obtain ⟨x, rfl⟩ := H x,
  exact ⟨is_localization.mk' R' x ⟨s, hs⟩, is_localization.map_mk' _ _ _⟩
end

lemma is_closed_immersion.affine_property_is_local :
  (is_closed_immersion.affine_property : _).is_local :=
is_local_affine_and _
  ring_hom.surjective_respects_iso
  ring_hom.localization_surjective
  ring_hom.surjective_of_localization_span

lemma is_closed_immersion_eq_affine_property : 
  @is_closed_immersion = target_affine_locally is_closed_immersion.affine_property :=
begin
  apply property_ext_of_le_affine is_closed_immersion_le_affine
    (by exact (target_affine_locally_affine_and_le_affine _)) is_closed_immersion_is_local_at_target
    is_closed_immersion.affine_property_is_local.target_affine_locally_is_local,
  simp_rw [is_closed_immersion.affine_property_is_local.affine_target_iff,
    is_closed_immersion.affine_property, affine_and_Spec_iff ring_hom.surjective_respects_iso],
  intros R S ϕ,
  refine ⟨λ h, by exactI surjective_of_is_closed_immersion ϕ, _⟩,
  { introI h,
    refine ⟨prime_spectrum.closed_embedding_comap_of_surjective _ _ h,
      (Top.presheaf.locally_surjective_iff_surjective_on_stalks _).mpr _⟩,
    rintro (x : prime_spectrum R),
    letI := ϕ.to_algebra,
    convert_to function.surjective (is_scalar_tower.to_alg_hom R
      ((Spec.structure_sheaf R).presheaf.stalk x) 
      ((Spec.Top_map (algebra_map R S) _* (Spec.structure_sheaf S).1).stalk x)).to_linear_map,
    have := Spec.localized_module_map_iso_stalk_map R S x,
    refine @function.surjective.of_comp _ _ _ _ ((is_localized_module.iso x.as_ideal.prime_compl
      (algebra.of_id R ((Spec.structure_sheaf R).presheaf.stalk x)).to_linear_map).to_linear_map) _,
    rw [← linear_map.coe_comp, ← this],
    apply function.surjective.comp,
    { exact (linear_equiv.to_equiv _).surjective },
    { exact linear_map.surjective_localized_module_map _ (algebra.of_id R S).to_linear_map h } }
end

lemma is_closed_immersion.affine_open_cover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
  tfae [is_closed_immersion f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)],
      ∀ (i : 𝒰.J), is_affine (pullback f (𝒰.map i)) ∧
        function.surjective (Scheme.Γ.map (pullback.snd : pullback f (𝒰.map i) ⟶ _).op),
    ∀ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)] (i : 𝒰.J),
      is_affine (pullback f (𝒰.map i)) ∧
        function.surjective (Scheme.Γ.map (pullback.snd : pullback f (𝒰.map i) ⟶ _).op),
    ∀ {U : Scheme} (g : U ⟶ Y) [is_affine U] [is_open_immersion g],
      is_affine (pullback f g) ∧
        function.surjective (Scheme.Γ.map (pullback.snd : pullback f g ⟶ _).op),
    ∃ {ι : Type u} (U : ι → opens Y.carrier) (hU : supr U = ⊤) (hU' : ∀ i, is_affine_open (U i)),
      ∀ i, is_affine_open ((opens.map f.1.base).obj $ U i) ∧
        function.surjective (f.1.c.app (op $ U i))] :=
begin
  rw is_closed_immersion_eq_affine_property,
  convert is_closed_immersion.affine_property_is_local.affine_open_cover_tfae f,
  delta is_closed_immersion.affine_property,
  ext ι,
  refine exists₃_congr (λ U hU hU', forall_congr $ λ i, and_congr iff.rfl _),
  dsimp only,
  rw [algebraic_geometry.Scheme.Γ_map, quiver.hom.unop_op, morphism_restrict_c_app, coe_comp],
  refine iff.trans _ (function.surjective.of_comp_iff' _ _).symm,
  { let V := (U i).open_embedding.is_open_map.functor.obj ⊤,
    show _ ↔ function.surjective (f.1.c.app (op V)),
    have e : V = _ := (U i).open_embedding_obj_top, clear_value V, subst e },
  { exact (as_iso $ X.presheaf.map (eq_to_hom _).op).CommRing_iso_to_ring_equiv.bijective }
end

lemma is_closed_immersion.is_local_at_target :
  property_is_local_at_target @is_closed_immersion :=
is_closed_immersion_eq_affine_property.symm ▸
  is_closed_immersion.affine_property_is_local.target_affine_locally_is_local

lemma is_closed_immersion.open_cover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
  tfae [is_closed_immersion f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y), ∀ (i : 𝒰.J),
      is_closed_immersion (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (𝒰 : Scheme.open_cover.{u} Y) (i : 𝒰.J),
      is_closed_immersion (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (U : opens Y.carrier), is_closed_immersion (f ∣_ U),
    ∀ {U : Scheme} (g : U ⟶ Y) [is_open_immersion g],
      is_closed_immersion (pullback.snd : pullback f g ⟶ _),
    ∃ {ι : Type u} (U : ι → opens Y.carrier) (hU : supr U = ⊤), ∀ i, is_closed_immersion (f ∣_ (U i))] :=
is_closed_immersion_eq_affine_property.symm ▸
  is_closed_immersion.affine_property_is_local.target_affine_locally_is_local.open_cover_tfae f

lemma is_closed_immersion_over_affine_iff {X Y : Scheme} (f : X ⟶ Y) [is_affine Y] :
  is_closed_immersion f ↔ is_affine X ∧ function.surjective (Scheme.Γ.map f.op) :=
is_closed_immersion_eq_affine_property.symm ▸
  is_closed_immersion.affine_property_is_local.affine_target_iff f

lemma is_closed_immersion_Spec_iff {R S : CommRing} (f : R ⟶ S) :
  is_closed_immersion (Scheme.Spec.map f.op) ↔ function.surjective f :=
begin
  rw [is_closed_immersion_eq_affine_property,
    is_closed_immersion.affine_property_is_local.affine_target_iff,
    is_closed_immersion.affine_property, affine_and_Spec_iff ring_hom.surjective_respects_iso]
end

local attribute [instance] mono_comp

lemma is_closed_immersion_le_mono : @is_closed_immersion ≤ @mono Scheme _ :=
begin
  rw [← is_closed_immersion_is_local_at_target.target_affine_locally_eq,
    ← mono_is_local_at_target.target_affine_locally_eq],
  apply target_affine_locally_mono,
  introsI X Y f _ H,
  haveI := is_affine_of_affine f,
  rw is_closed_immersion_over_affine_iff at H,
  haveI := (forget CommRing).epi_of_epi_map ((epi_iff_surjective _).mpr H.2),
  have := Γ_Spec.adjunction.unit_naturality f,
  rw [functor.right_op_map, ← is_iso.comp_inv_eq] at this,
  rw ← this,
  apply_instance
end

@[priority 100]
instance is_closed_immersion.to_mono [is_closed_immersion f] : mono f :=
is_closed_immersion_le_mono _ _ f infer_instance

lemma is_closed_immersion.affine_open_cover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.open_cover.{u} Y)
  [∀ i, is_affine (𝒰.obj i)] (f : X ⟶ Y) :
  is_closed_immersion f ↔ ∀ i, is_affine (pullback f (𝒰.map i)) ∧
        function.surjective (Scheme.Γ.map (pullback.snd : pullback f (𝒰.map i) ⟶ _).op) :=
is_closed_immersion_eq_affine_property.symm ▸
  is_closed_immersion.affine_property_is_local.affine_open_cover_iff f 𝒰

lemma is_closed_immersion.open_cover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.open_cover.{u} Y) (f : X ⟶ Y) :
  is_closed_immersion f ↔ ∀ i, is_closed_immersion (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
is_closed_immersion_eq_affine_property.symm ▸
  is_closed_immersion.affine_property_is_local.target_affine_locally_is_local.open_cover_iff f 𝒰

instance [is_closed_immersion f] [is_closed_immersion g] : is_closed_immersion (f ≫ g) :=
is_closed_immersion_stable_under_composition _ _ infer_instance infer_instance

lemma is_closed_immersion_stable_under_base_change : 
  morphism_property.stable_under_base_change @is_closed_immersion := 
begin
  rw is_closed_immersion_eq_affine_property,
  exact affine_and_stable_under_base_change _ ring_hom.surjective_respects_iso
    ring_hom.localization_surjective ring_hom.surjective_of_localization_span
    ring_hom.surjective_stable_under_base_change,
end

instance (f : X ⟶ Z) (g : Y ⟶ Z) [is_closed_immersion g] :
  is_closed_immersion (pullback.fst : pullback f g ⟶ X) :=
is_closed_immersion_stable_under_base_change.fst f g infer_instance

instance (f : X ⟶ Z) (g : Y ⟶ Z) [is_closed_immersion f] :
  is_closed_immersion (pullback.snd : pullback f g ⟶ Y) :=
is_closed_immersion_stable_under_base_change.snd f g infer_instance

end algebraic_geometry

