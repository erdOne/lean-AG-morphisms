import morphisms.basic
import algebraic_geometry.surjective_on_stalks

/-!

# Locally closed immersions

A morphism of schemes is a closed immersion if the underlying map is a closed embedding, and 
the sheaf map is locally surjective.

-/

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universe u

namespace algebraic_geometry

variables {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)


/-- A morphism `is_preimmersion` if the underlying map is an topological embedding, and 
the map on stalks is surjective. -/
@[mk_iff]
class is_preimmersion (f : X ⟶ Y) : Prop :=
(base_embedding [] : embedding f.1.base)
(stalk_map_surjective [] : ∀ x, function.surjective (PresheafedSpace.stalk_map f.1 x))

instance [is_preimmersion f] [is_preimmersion g] : is_preimmersion (f ≫ g) :=
begin
  constructor,
  { exact (is_preimmersion.base_embedding g).comp (is_preimmersion.base_embedding f) },
  { intro x, erw PresheafedSpace.stalk_map.comp f.1 g.1 x,
    exact (is_preimmersion.stalk_map_surjective f _).comp
      (is_preimmersion.stalk_map_surjective g _) }
end

instance is_open_immersion.to_is_preimmersion [is_open_immersion f] : is_preimmersion f :=
begin
  constructor,
  { exact (is_open_immersion.base_open f).to_embedding },
  { exact λ x, (as_iso $ PresheafedSpace.stalk_map f.1 x).CommRing_iso_to_ring_equiv.surjective }
end

lemma is_preimmersion.of_comp [is_preimmersion (f ≫ g)] :
  is_preimmersion f :=
begin
  constructor,
  { exact embedding_of_embedding_compose f.1.base.2 g.1.base.2
      (is_preimmersion.base_embedding $ f ≫ g) },
  { intro x,
    have := (is_preimmersion.stalk_map_surjective $ f ≫ g) x,
    erw PresheafedSpace.stalk_map.comp at this,
    rw coe_comp at this,
    exact function.surjective.of_comp this }
end

universes w v

lemma Top.sheaf.hom_stalk_ext {X : Top.{v}} {C : Type u} [category.{v} C]
  [concrete_category.{v} C] [has_colimits C]
  [preserves_filtered_colimits (forget C)]
  [has_limits C] [preserves_limits (forget C)] [reflects_isomorphisms (forget C)]
  {F G : X.sheaf C}
  (α β : F ⟶ G)
  (h : ∀ x, (Top.presheaf.stalk_functor C x).map α.1 = (Top.presheaf.stalk_functor C x).map β.1) :
  α = β :=
begin
  ext U,
  induction U,
  apply concrete_category.hom_ext,
  intros s,
  apply Top.presheaf.section_ext G U,
  intro x,
  rw [← Top.presheaf.stalk_functor_map_germ_apply, ← Top.presheaf.stalk_functor_map_germ_apply, h],
end

lemma SheafedSpace.hom_stalk_ext {C : Type u} [category.{v} C]
  [concrete_category.{v} C] [has_colimits C]
  [preserves_filtered_colimits (forget C)]
  [has_limits C] [preserves_limits (forget C)] [reflects_isomorphisms (forget C)]
  {X Y : SheafedSpace C}
  (f g : X ⟶ Y)
  (h : f.base = g.base)
  (h' : ∀ x, PresheafedSpace.stalk_map f x =
    Y.presheaf.stalk_specializes (specializes_of_eq $ by rw h) ≫ PresheafedSpace.stalk_map g x) :
  f = g :=
begin
  cases f, cases g,
  obtain (rfl : f_base = g_base) := h,
  suffices : f_c = g_c, { subst this },
  ext U,
  induction U,
  apply concrete_category.hom_ext,
  intros s,
  apply Top.presheaf.section_ext X.sheaf ((opens.map f_base).obj U),
  intro x,
  delta SheafedSpace.sheaf Top.sheaf.presheaf,
  dsimp only,
  erw [← PresheafedSpace.stalk_map_germ_apply ⟨f_base, f_c⟩,
    ← PresheafedSpace.stalk_map_germ_apply ⟨f_base, g_c⟩, h'],
  simp only [Top.presheaf.stalk_specializes_refl, category.id_comp,
    PresheafedSpace.stalk_map_germ_apply],
end

lemma SheafedSpace.mono_of_base_injective_of_stalk_epi
  {C : Type u} [category.{v} C]
  [concrete_category.{v} C] [has_colimits C]
  [preserves_filtered_colimits (forget C)]
  [has_limits C] [preserves_limits (forget C)] [reflects_isomorphisms (forget C)]
  {X Y : SheafedSpace C}
  (f : X ⟶ Y)
  (h₁ : function.injective f.base)
  (h₂ : ∀ x, epi (PresheafedSpace.stalk_map f x)) : mono f :=
begin
  constructor,
  introsI Z g h e,
  have : g.base = h.base,
  { rw ← Top.mono_iff_injective at h₁, resetI,
    simp only [← cancel_mono f.base, ← SheafedSpace.comp_base, e] },
  apply SheafedSpace.hom_stalk_ext _ _ this,
  intro x,
  cases g, cases h, obtain (rfl : g_base = h_base) := this,
  rw [← cancel_epi (PresheafedSpace.stalk_map f (g_base x)), Top.presheaf.stalk_specializes_refl,
  category.id_comp],
  rw [← PresheafedSpace.stalk_map.comp ⟨g_base, g_c⟩ f,
    ← PresheafedSpace.stalk_map.comp ⟨g_base, h_c⟩ f],
  congr, exact e,
end

instance is_preimmersion.to_mono [is_preimmersion f] : mono f :=
begin
  refine (Scheme.forget_to_LocallyRingedSpace ⋙
    LocallyRingedSpace.forget_to_SheafedSpace).mono_of_mono_map _,
  apply SheafedSpace.mono_of_base_injective_of_stalk_epi,
  { exact (is_preimmersion.base_embedding f).inj },
  { intro x, 
    apply (forget CommRing).epi_of_epi_map,
    rw epi_iff_surjective,
    exact (is_preimmersion.stalk_map_surjective f x : _) }
end

lemma is_preimmersion_stable_under_composition : 
  morphism_property.stable_under_composition @is_preimmersion :=
λ _ _ _ _ _ _ _, by exactI infer_instance

lemma is_preimmersion_respects_iso : 
  morphism_property.respects_iso @is_preimmersion :=
is_preimmersion_stable_under_composition.respects_iso (λ _ _ _, infer_instance)

lemma is_preimmersion_is_local_at_target :
  property_is_local_at_target @is_preimmersion :=
begin
  constructor,
  { exact is_preimmersion_respects_iso },
  { introsI X Y f U H,
    constructor,
    { rw morphism_restrict_val_base, exact H.1.restrict_preimage U.1 },
    { exact λ x, ((morphism_property.surjective_respects_iso _).arrow_iso_iff
      (morphism_restrict_stalk_map f U x)).mpr (H.2 x.1) } },
  { intros X Y f 𝒰 H,
    constructor,
    { apply (embedding_iff_embedding_of_supr_eq_top
        𝒰.supr_opens_range f.1.base.2).mpr,
      intro i,
      have := ((is_preimmersion_respects_iso.arrow_iso_iff
        (morphism_restrict_opens_range f (𝒰.map i))).mpr (H i)).1,
      rwa [arrow.mk_hom, morphism_restrict_val_base] at this },
    { exact λ x, ((morphism_property.surjective_respects_iso _).arrow_iso_iff
        (morphism_restrict_stalk_map f _ _)).mp
        (((is_preimmersion_respects_iso.arrow_iso_iff (morphism_restrict_opens_range f (𝒰.map _)))
        .mpr (H (𝒰.f $ f.1.base x))).2 ⟨x, 𝒰.covers (f.1.base x)⟩) } }
end

lemma is_preimmersion_open_cover_tfae (f : X ⟶ Y) :
  tfae [is_preimmersion f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y), ∀ (i : 𝒰.J),
      is_preimmersion (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (𝒰 : Scheme.open_cover.{u} Y) (i : 𝒰.J),
      is_preimmersion (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (U : opens Y.carrier), is_preimmersion (f ∣_ U),
    ∀ {U : Scheme} (g : U ⟶ Y) [is_open_immersion g],
      is_preimmersion (pullback.snd : pullback f g ⟶ U),
    ∃ {ι : Type u} (U : ι → opens Y.carrier) (hU : supr U = ⊤),
      (∀ i, is_preimmersion (f ∣_ (U i)))] :=
is_preimmersion_is_local_at_target.open_cover_tfae f

lemma is_preimmersion_stable_under_base_change :
  morphism_property.stable_under_base_change @is_preimmersion :=
morphism_property.stable_under_base_change.mk is_preimmersion_respects_iso 
begin
  intros X Y S f g hg,
  refine ⟨_, pullback_snd_surjective_on_stalks f g hg.2⟩,
  rw ← (pullback_comparison_comp_fst Scheme.forget_to_Top f g).trans (Scheme.forget_to_Top_map' _),
  exact (Top.fst_embedding_of_right_embedding f.1.base hg.1).comp
    (embedding_category_theory_pullback_comparison_of_surjective_on_stalks f g hg.2)
end

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [is_preimmersion g] :
  is_preimmersion (pullback.fst : pullback f g ⟶ X) :=
is_preimmersion_stable_under_base_change.fst f g infer_instance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [is_preimmersion f] :
  is_preimmersion (pullback.snd : pullback f g ⟶ Y) :=
is_preimmersion_stable_under_base_change.snd f g infer_instance

lemma is_preimmersion_Spec_of_exists_eq_div {R S : CommRing} (f : R ⟶ S) 
  (hf : ∀ x : S, ∃ a b : R, is_unit (f b) ∧ x * f b = f a) :
  is_preimmersion (Scheme.Spec.map f.op) :=
begin
  constructor,
  { have H : ∀ x : (is_unit.submonoid S).comap f, is_unit (f x) := subtype.prop, 
    have : (is_localization.lift H).comp (algebra_map R $ localization $
      (is_unit.submonoid S).comap f) = f := is_localization.lift_comp H,
    rw [Scheme.Spec_map_val_base, ← this, prime_spectrum.comap_comp],
    refine (prime_spectrum.localization_comap_embedding (localization $
      (is_unit.submonoid S).comap f) ((is_unit.submonoid S).comap f)).comp 
      (prime_spectrum.closed_embedding_comap_of_surjective _ _ _).to_embedding,
    rintro (x : S),
    obtain ⟨a, b, hb, e⟩ := hf x,
    refine ⟨is_localization.mk' _ a ⟨b, show b ∈ ((is_unit.submonoid S).comap f), from hb⟩, _⟩,
    rwa [is_localization.lift_mk'_spec, subtype.coe_mk, eq_comm, mul_comm] },
  { intro x, 
    refine ((morphism_property.surjective_respects_iso CommRing).arrow_mk_iso_iff
      (Spec.stalk_map_iso _ x)).mpr _,
    exact ring_hom.surjective_on_stalks_of_exists_eq_div hf x.as_ideal }
end

attribute [reassoc] Top.presheaf.germ_res

instance (x) : is_preimmersion (X.from_Spec_stalk x) :=
begin
  delta Scheme.from_Spec_stalk is_affine_open.from_Spec_stalk,
  apply is_preimmersion_stable_under_composition,
  { apply is_preimmersion_Spec_of_exists_eq_div,
    rintro (y : X.presheaf.stalk x),
    let R := X.affine_cover_ring x,
    obtain ⟨x' : prime_spectrum R, hx⟩ := X.affine_cover.covers x,
    let e : X.presheaf.stalk x ≅ (Spec.structure_sheaf R).presheaf.stalk x' :=
      X.presheaf.stalk_congr (inseparable.of_eq hx.symm)
        ≪≫ (as_iso $ PresheafedSpace.stalk_map (X.affine_cover.map x).1 x'),
    let e' : R ≅ X.presheaf.obj (op $ (X.affine_cover.map x).opens_range) :=
      (as_iso $ to_Spec_Γ R) ≪≫ (as_iso $ (X.affine_cover.is_open x).inv_app ⊤) ≪≫
        X.presheaf.map_iso (eq_to_iso $ opens.ext $ by exact set.image_univ.symm).op,
    have : e'.hom ≫ X.presheaf.germ ⟨x, X.affine_cover.covers x⟩ ≫ e.hom =
      structure_sheaf.to_stalk R x',
    { simp only [iso.trans_hom, category.assoc, as_iso_hom, functor.map_iso_hom,
        Top.presheaf.stalk_congr_hom, iso.op_hom, Top.presheaf.germ_res_assoc,
        Top.presheaf.germ_stalk_specializes'_assoc, structure_sheaf.to_stalk],
      erw [PresheafedSpace.stalk_map_germ', PresheafedSpace.is_open_immersion.inv_app_app_assoc],
      congr' 1,
      refine (X.affine_cover.obj x).presheaf.germ_res (eq_to_hom _) ⟨_, _⟩,
      exact opens.map_functor_eq' _ (is_open_immersion.base_open _) _ },
    obtain ⟨⟨z, s⟩, hz⟩ := is_localization.surj x'.as_ideal.prime_compl (e.hom y),
    refine ⟨e'.hom z, e'.hom s, _, _⟩,
    { apply is_unit_of_map_unit e.hom, simp only [← comp_apply, category.assoc], erw this,
      exact is_localization.map_units ((Spec.structure_sheaf R).presheaf.stalk x') s },
    { apply (show function.injective e.hom, from e.CommRing_iso_to_ring_equiv.injective),
      simp only [← comp_apply, category.assoc, map_mul, iso.CommRing_iso_to_ring_equiv],
      erw this,
      exact hz } },
  { apply_instance }
end

end algebraic_geometry
