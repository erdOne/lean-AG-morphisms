
/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import morphisms.open_immersion
import morphisms.closed_immersion
import for_mathlib.locally_closed
import algebraic_geometry.pullback_carrier

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


/-- A morphism is a `is_closed_immersion` if the preimages of affine open sets are affine. -/
@[mk_iff]
class is_immersion (f : X ⟶ Y) : Prop :=
(base_embedding [] : embedding f.1.base)
(range_is_locally_closed [] : is_locally_closed (set.range f.1.base))
(stalk_map_surjective [] : ∀ x, function.surjective (PresheafedSpace.stalk_map f.1 x))

instance [is_immersion f] [is_immersion g] : is_immersion (f ≫ g) :=
begin
  constructor,
  { exact (is_immersion.base_embedding g).comp (is_immersion.base_embedding f) },
  { rw [Scheme.comp_val_base, coe_comp, set.range_comp],
    exact (is_immersion.range_is_locally_closed f).image (is_immersion.base_embedding g).to_inducing
      (is_immersion.range_is_locally_closed g) },
  { intro x, erw PresheafedSpace.stalk_map.comp f.1 g.1 x,
    exact (is_immersion.stalk_map_surjective f _).comp (is_immersion.stalk_map_surjective g _) }
end

-- move me
lemma is_open_immersion.base_open [H : is_open_immersion f] : open_embedding f.1.base :=
H.1

instance is_open_immersion.to_is_immersion [is_open_immersion f] : is_immersion f :=
begin
  constructor,
  { exact (is_open_immersion.base_open f).to_embedding },
  { exact (is_open_immersion.base_open f).2.is_locally_closed },
  { exact λ x, (as_iso $ PresheafedSpace.stalk_map f.1 x).CommRing_iso_to_ring_equiv.surjective }
end

instance is_closed_immersion.to_is_immersion [is_closed_immersion f] : is_immersion f :=
begin
  constructor,
  { exact (is_closed_immersion.base_closed f).to_embedding },
  { exact (is_closed_immersion.base_closed f).2.is_locally_closed },
  { exact is_closed_immersion.stalk_map_surjective f }
end

lemma is_closed_immersion.of_is_immersion [is_immersion f] (hf : is_closed (set.range f.1.base)) :
  is_closed_immersion f :=
begin
  rw is_closed_immersion_iff_stalk,
  exact ⟨⟨is_immersion.base_embedding f, hf⟩, is_immersion.stalk_map_surjective f⟩
end

-- In fact it still holds if `g` is topologically a locally closed embedding
lemma is_immersion.of_comp_of_is_immersion [is_immersion (f ≫ g)] [is_immersion g] :
  is_immersion f :=
begin
  constructor,
  { exact embedding_of_embedding_compose f.1.base.2 g.1.base.2
      (is_immersion.base_embedding $ f ≫ g) },
  { rw (is_immersion.base_embedding g).to_inducing.is_locally_closed_iff,
    refine ⟨_, is_immersion.range_is_locally_closed (f ≫ g), _⟩,
    rw [Scheme.comp_val_base, coe_comp, set.range_comp],
    exact set.preimage_image_eq (set.range f.1.base) (is_immersion.base_embedding g).inj },
  { intro x,
    have := (is_immersion.stalk_map_surjective $ f ≫ g) x,
    erw PresheafedSpace.stalk_map.comp at this,
    rw coe_comp at this,
    exact function.surjective.of_comp this }
end

@[simps]
def is_immersion.factor_opens [is_immersion f] : opens Y.carrier :=
⟨_, (is_immersion.range_is_locally_closed f).is_open_coboundary⟩

def is_immersion.factor_open_subscheme [is_immersion f] : Scheme :=
Y.restrict (is_immersion.factor_opens f).open_embedding

@[derive is_open_immersion]
def is_immersion.factor_open_immersion [is_immersion f] :
  is_immersion.factor_open_subscheme f ⟶ Y :=
Y.of_restrict _

-- move me
lemma opens.range_inclusion {X : Top} (U : opens X) : set.range U.inclusion = U :=
subtype.range_coe

def is_immersion.factor_closed_immersion [is_immersion f] :
  X ⟶ is_immersion.factor_open_subscheme f :=
is_open_immersion.lift (is_immersion.factor_open_immersion f) f
begin
  rw [is_immersion.factor_open_immersion, Scheme.of_restrict_val_base, opens.range_inclusion],
  exact subset_coboundary
end

@[simp, reassoc]
lemma is_immersion.factors [is_immersion f] :
  is_immersion.factor_closed_immersion f ≫ is_immersion.factor_open_immersion f = f :=
is_open_immersion.lift_fac _ _ _

-- move me
lemma is_open_immersion.range_lift (f : X ⟶ Z) (g : Y ⟶ Z) [is_open_immersion f] 
  (H : set.range g.1.base ⊆ set.range f.1.base) :
  set.range (is_open_immersion.lift f g H).1.base = f.1.base ⁻¹' (set.range g.1.base) :=
LocallyRingedSpace.is_open_immersion.lift_range _ _ _

instance [is_immersion f] : is_closed_immersion (is_immersion.factor_closed_immersion f) :=
begin
  haveI : is_immersion (is_immersion.factor_closed_immersion f),
  { apply_with (is_immersion.of_comp_of_is_immersion _ (is_immersion.factor_open_immersion f))
    { instances := ff },
    rwa is_immersion.factors },
  apply is_closed_immersion.of_is_immersion,
  rw [is_immersion.factor_closed_immersion, is_open_immersion.range_lift],
  exact is_closed_preimage_coe_coboundary
end

lemma is_immersion_iff_exists_factor : 
  is_immersion f ↔ ∃ {Z : Scheme} (g : X ⟶ Z) [is_closed_immersion g]
    (h : Z ⟶ Y) [is_open_immersion h], g ≫ h = f :=
begin
  split,
  { introI H, exact ⟨_, is_immersion.factor_closed_immersion f, infer_instance,
      is_immersion.factor_open_immersion f, infer_instance, is_immersion.factors f⟩ },
  { rintro ⟨_, _, _, _, _, rfl⟩, by exactI infer_instance }
end

instance [is_immersion f] : mono f :=
by { rw ← is_immersion.factors f, apply mono_comp }

lemma is_immersion_stable_under_composition : 
  morphism_property.stable_under_composition @is_immersion :=
λ _ _ _ _ _ _ _, by exactI infer_instance

lemma is_immersion_respects_iso : 
  morphism_property.respects_iso @is_immersion :=
is_immersion_stable_under_composition.respects_iso (λ _ _ _, infer_instance)

lemma is_immersion_stable_under_base_change :
  morphism_property.stable_under_base_change @is_immersion :=
begin
  intros X Y X' S f g f' g' H hg,
  rw is_immersion_iff_exists_factor at hg ⊢,
  obtain ⟨Z, i₁, _, i₂, _, rfl⟩ := hg,
  resetI,
  refine ⟨pullback i₂ f, pullback.lift (f' ≫ i₁) g' ((category.assoc _ _ _).trans H.w), _,
    pullback.snd, infer_instance, pullback.lift_snd _ _ _⟩,
  have : is_pullback f'
    (pullback.lift (f' ≫ i₁) g' ((category.assoc _ _ _).trans H.w)) i₁ pullback.fst :=
    is_pullback.of_bot (by rwa pullback.lift_snd)
      (pullback.lift_fst _ _ _).symm (is_pullback.of_has_pullback _ _),
  exact is_closed_immersion_stable_under_base_change this infer_instance
end

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [is_immersion g] :
  is_immersion (pullback.fst : pullback f g ⟶ X) :=
is_immersion_stable_under_base_change.fst f g infer_instance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [is_immersion f] :
  is_immersion (pullback.snd : pullback f g ⟶ Y) :=
is_immersion_stable_under_base_change.snd f g infer_instance

lemma is_immersion_is_local_at_target :
  property_is_local_at_target @is_immersion :=
begin
  constructor,
  { exact is_immersion_respects_iso },
  { introsI X Y f U H,
    constructor,
    { rw morphism_restrict_val_base, exact H.1.restrict_preimage U.1 },
    { rw [morphism_restrict_val_base, set.range_restrict_preimage],
      exact (is_immersion.range_is_locally_closed f).preimage continuous_subtype_coe },
    { exact λ x, ((morphism_property.surjective_respects_iso _).arrow_iso_iff
      (morphism_restrict_stalk_map f U x)).mpr (H.3 x.1) } },
  { intros X Y f 𝒰 H,
    constructor,
    { apply (embedding_iff_embedding_of_supr_eq_top
        𝒰.supr_opens_range f.1.base.2).mpr,
      intro i,
      have := ((is_immersion_respects_iso.arrow_iso_iff
        (morphism_restrict_opens_range f (𝒰.map i))).mpr (H i)).1,
      rwa [arrow.mk_hom, morphism_restrict_val_base] at this },
    { rw is_locally_closed_iff_coe_preimage_of_supr_eq_top 𝒰.supr_opens_range,
      intro i, 
      replace H := (H i).2,
      simp_rw [pullback.range_snd, (is_open_immersion.base_open $ 𝒰.map i).to_embedding
        .is_locally_closed_iff, set.image_preimage_eq_inter_range] at H,
      obtain ⟨s, hs, hs'⟩ := H,
      rw embedding_subtype_coe.is_locally_closed_iff,
      refine ⟨s, hs, _⟩,
      rwa [set.image_preimage_eq_inter_range, @subtype.range_coe _ (set.range _)] },
    { exact λ x, ((morphism_property.surjective_respects_iso _).arrow_iso_iff
        (morphism_restrict_stalk_map f _ _)).mp
        (((is_immersion_respects_iso.arrow_iso_iff (morphism_restrict_opens_range f (𝒰.map _)))
        .mpr (H (𝒰.f $ f.1.base x))).3 ⟨x, 𝒰.covers (f.1.base x)⟩) } }
end
.

lemma is_immersion_open_cover_tfae (f : X ⟶ Y) :
  tfae [is_immersion f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y), ∀ (i : 𝒰.J),
      is_immersion (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (𝒰 : Scheme.open_cover.{u} Y) (i : 𝒰.J),
      is_immersion (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (U : opens Y.carrier), is_immersion (f ∣_ U),
    ∀ {U : Scheme} (g : U ⟶ Y) [is_open_immersion g],
      is_immersion (pullback.snd : pullback f g ⟶ U),
    ∃ {ι : Type u} (U : ι → opens Y.carrier) (hU : supr U = ⊤), (∀ i, is_immersion (f ∣_ (U i)))] :=
is_immersion_is_local_at_target.open_cover_tfae f

lemma is_immersion_open_cover_of_subset_supr (f : X ⟶ Y)
  {ι : Type u} (U : ι → opens Y.carrier) (hU : set.range f.1.base ⊆ ((supr U : _) : set Y.carrier))
  (h : ∀ i, is_immersion (f ∣_ U i)) : is_immersion f :=
begin
  let V := supr U,
  have hV : (opens.map f.val.base).obj V = ⊤,
  { rw [eq_top_iff], exact set.image_subset_iff.mp ((subset_of_eq set.image_univ).trans hU) },
  suffices : is_immersion (f ∣_ V),
  { haveI : is_iso (X.of_restrict ((opens.map f.val.base).obj V).open_embedding),
    { rw hV,
      apply_with (is_iso_of_reflects_iso _ Scheme.forget_to_LocallyRingedSpace) { instances := ff },
      convert_to is_iso X.to_LocallyRingedSpace.restrict_top_iso.hom,
      apply_instance },
    rw [← is_immersion_respects_iso.cancel_left_is_iso
      (X.of_restrict ((opens.map f.val.base).obj V).open_embedding), ← morphism_restrict_ι],
    apply_instance },
  let U' : ι → opens (Y.restrict V.open_embedding).carrier := (opens.map V.inclusion).obj ∘ U,
  have : supr U' = ⊤,
  { rw [eq_top_iff],
    rintro ⟨x, hx⟩ -,
    obtain ⟨i, hi⟩ := opens.mem_supr.mp hx,
    exact opens.mem_supr.mpr ⟨i, hi⟩ },
  refine ((is_immersion_open_cover_tfae (f ∣_ V)).out 0 5).mpr ⟨_, U', this, λ i, _⟩,
  refine (is_immersion_respects_iso.arrow_iso_iff (morphism_restrict_restrict f _ _ ≪≫
    morphism_restrict_eq f ((V.functor_map_eq_inf _).trans _))).mpr (h i),
  rw inf_eq_left,
  exact le_supr U i,
end

lemma is_closed_immersion_pullback_diagonal_Spec {R S : CommRing}
  (f' : Scheme.Spec.obj (op S) ⟶ Scheme.Spec.obj (op R)) :
  is_closed_immersion (pullback.diagonal f') :=
begin
  let f : R ⟶ S := (Scheme.Spec.preimage f').unop,
  have : Scheme.Spec.map f.op = f', { rw [quiver.hom.op_unop, functor.image_preimage] },
  clear_value f, subst this,
  letI := f.to_algebra,
  have H := (is_pushout.of_is_colimit
    (CommRing.pushout_cocone_is_colimit f f)).op.map Scheme.Spec,
  let e : pullback.diagonal_obj (Scheme.Spec.map f.op) ≅ 
    Scheme.Spec.obj (op (CommRing.pushout_cocone f f).X) := limit.iso_limit_cone ⟨_, H.is_limit⟩,
  have : pullback.diagonal _ ≫ e.hom = Scheme.Spec.map
    (quiver.hom.op $ (@algebra.tensor_product.lmul' R S _ _ _).to_ring_hom),
  { apply pullback_cone.is_limit.hom_ext H.is_limit,
    { rw category.assoc,
      erw [is_limit.cone_point_unique_up_to_iso_hom_comp, pullback.diagonal_fst],
      rw [H.cone_fst, ← functor.map_comp, ← op_comp],
      transitivity Scheme.Spec.map (𝟙 _).op, { rw [op_id, category_theory.functor.map_id] },
      congr' 2, ext1, simp },
    { rw category.assoc,
      erw [is_limit.cone_point_unique_up_to_iso_hom_comp, pullback.diagonal_snd],
      rw [H.cone_snd, ← functor.map_comp, ← op_comp],
      transitivity Scheme.Spec.map (𝟙 _).op, { rw [op_id, category_theory.functor.map_id] },
      congr' 2, ext1, simp }, }, 
  rw [← is_closed_immersion_respects_iso.cancel_right_is_iso _ e.hom, this,
    is_closed_immersion_Spec_iff],
  exact λ x, ⟨x ⊗ₜ 1, (algebra.tensor_product.lmul'_apply_tmul _ _).trans (mul_one _)⟩,
end

local attribute [irreducible] Scheme.affine_cover

-- Declaring it as an instance adds superfluous universe variables
@[instance]
lemma _root_.category_theory.limits.pullback.diagonal.is_immersion {X Y : Scheme.{u}} (f : X ⟶ Y) :
  is_immersion (pullback.diagonal f) :=
begin
  let 𝒱 := λ i, (pullback f (Y.affine_cover.map i)).affine_cover,
  let 𝒰 : (pullback f f).open_cover := (Scheme.pullback.open_cover_of_base Y.affine_cover _ _).bind
    (λ i, Scheme.pullback.open_cover_of_left_right (𝒱 i) (𝒱 i) pullback.snd pullback.snd),
  let I := Σ (i : Y.affine_cover.J), (𝒱 i).J,
  let 𝒰' := λ (i : I), (𝒰.map ⟨i.1, i.2, i.2⟩).opens_range, 
  have : set.range (pullback.diagonal f).1.base ⊆ ((supr 𝒰' : _) : set (pullback f f).carrier),
  { rintros _ ⟨x, rfl⟩,
    let i := Y.affine_cover.f (f.1.base x),
    obtain ⟨y, hy : (Y.affine_cover.map i).1.base y = _⟩ := Y.affine_cover.covers (f.1.base x),
    let T : pullback.triplet f (Y.affine_cover.map i) := ⟨x, y, _, rfl, hy⟩,
    obtain ⟨z, (hzx : _ = x), (rfl : _ = y)⟩ := T.exists_preimage,
    obtain ⟨w, hw⟩ := (𝒱 i).covers z,
    rw [← hzx, ← hw],
    refine opens.mem_supr.mpr ⟨⟨i, (𝒱 i).f z⟩,
      (pullback.diagonal ((𝒱 i).map ((𝒱 i).f z) ≫ pullback.snd)).1.base w, _⟩,
    simp_rw [← Scheme.comp_val_base_apply],
    congr' 3,
    dsimp [𝒰],
      apply pullback.hom_ext; simp only [category.assoc, pullback.lift_fst, pullback.lift_snd,  
          pullback.lift_fst_assoc, pullback.lift_snd_assoc,
          pullback.diagonal_fst_assoc, pullback.diagonal_fst,
          pullback.diagonal_snd_assoc, pullback.diagonal_snd, category.comp_id] },
  apply is_immersion_open_cover_of_subset_supr _ _ this,
  rintro ⟨i, j⟩,
  have : arrow.mk (pullback.diagonal f ∣_ 𝒰' ⟨i, j⟩) ≅
    arrow.mk (pullback.diagonal ((𝒱 i).map j ≫ pullback.snd)),
  { refine (morphism_restrict_opens_range _ _) ≪≫ arrow.iso_mk _ _ _,
    { dsimp [𝒰], 
      refine pullback.congr_hom rfl _ ≪≫
        pullback_diagonal_map_iso f (Y.affine_cover.map i) ((𝒱 i).map j) ((𝒱 i).map j) ≪≫
        as_iso pullback.fst,
      apply pullback.hom_ext; simp only [category.assoc, pullback.lift_fst, pullback.lift_snd,  
          pullback.lift_fst_assoc, pullback.lift_snd_assoc],
       },
    { dsimp [𝒰], exact iso.refl _ },
    { have : (pullback.fst : pullback ((𝒱 i).map j) ((𝒱 i).map j) ⟶ _) = pullback.snd,
      { rw ← cancel_epi (pullback.diagonal $ (𝒱 i).map j),
        rw [pullback.diagonal_fst, pullback.diagonal_snd] },
      dsimp [𝒰],
      apply pullback.hom_ext,
      swap, simp only [this],
      all_goals { simp only [category.assoc, pullback.lift_fst, pullback.lift_snd,  
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, category.id_comp, category.comp_id,
        pullback_diagonal_map_iso_hom_fst, pullback_diagonal_map_iso_hom_snd,
        pullback.diagonal_fst, pullback.diagonal_snd] } } },
  apply (is_immersion_respects_iso.arrow_iso_iff this).mpr _,
  apply_with is_closed_immersion.to_is_immersion { instances := ff },
  dsimp only [𝒱, Scheme.affine_cover],
  apply is_closed_immersion_pullback_diagonal_Spec,
end

end algebraic_geometry
