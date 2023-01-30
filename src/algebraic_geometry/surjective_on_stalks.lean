import algebraic_geometry.pullback_carrier
import for_mathlib.surjective_on_stalks
import algebraic_geometry.pushforward_stalk
import topology.local_at_target
import category_theory.morphism_property

open category_theory category_theory.limits topological_space opposite

namespace algebraic_geometry

universe u

noncomputable theory

variables {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
variable (hg : ∀ y : Y.carrier, function.surjective (PresheafedSpace.stalk_map g.1 y))

@[simps apply_coe_fst apply_coe_snd]
def pullback_comparison : 
  (pullback f g).carrier ⟶ Top.of (types.pullback_obj f.1.base g.1.base) :=
(Top.pullback_cone_is_limit f.1.base g.1.base).lift
  (pullback_cone.mk (pullback.fst : pullback f g ⟶ _).1.base
    (pullback.snd : pullback f g ⟶ _).1.base
    (by simp only [← Scheme.comp_val_base, pullback.condition]))

lemma pullback_comparison_comp_pullback_iso_prod_subtype_inv :
  pullback_comparison f g ≫ (Top.pullback_iso_prod_subtype f.1.base g.1.base).inv =
  category_theory.limits.pullback_comparison Scheme.forget_to_Top f g :=
begin
  apply pullback.hom_ext; simp only [pullback_comparison, category.assoc,
    Top.pullback_iso_prod_subtype_inv_fst, Top.pullback_iso_prod_subtype_inv_snd,
      pullback_comparison_comp_fst, pullback_comparison_comp_snd],
  exacts [(Top.pullback_cone_is_limit f.1.base g.1.base).fac _ walking_cospan.left,
    (Top.pullback_cone_is_limit f.1.base g.1.base).fac _ walking_cospan.right]
end

-- move me
@[simps]
def pullback.triplet_mk {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) (x : X.carrier) (y : Y.carrier)
  (h : f.1.base x = g.1.base y) : pullback.triplet f g :=
⟨x, y, _, h, rfl⟩

lemma is_open_immersion.base_open [is_open_immersion f] : open_embedding f.1.base :=
PresheafedSpace.is_open_immersion.base_open

lemma Scheme.Spec_map_val_base {R S : CommRing} (f : R ⟶ S) : 
  (Scheme.Spec.map f.op).1.base = prime_spectrum.comap f := rfl

section open_cover

-- move me
/-- The coordinate ring of a component in the `affine_cover`. -/
def Scheme.affine_cover_ring (X : Scheme) (i : X.affine_cover.J) : CommRing :=
CommRing.of $ (X.local_affine i).some_spec.some

-- move me
lemma Scheme.affine_cover_obj (X : Scheme) (i : X.affine_cover.J) :
  X.affine_cover.obj i = Scheme.Spec.obj (op $ X.affine_cover_ring i) := rfl

-- local attribute [irreducible] Scheme.affine_cover

def pullback_affine_cover : Scheme.open_cover.{u} (pullback f g) := 
  (Scheme.pullback.open_cover_of_base.{u u u} Z.affine_cover f g).bind
    (λ i, Scheme.pullback.open_cover_of_left_right.{u u u u}
      (pullback f (Z.affine_cover.map i)).affine_cover
      (pullback g (Z.affine_cover.map i)).affine_cover pullback.snd pullback.snd)

variable (i : (pullback_affine_cover f g).J)

def pullback_affine_cover_ring_left : CommRing :=
Scheme.affine_cover_ring _ i.2.1

def pullback_affine_cover_ring_right : CommRing :=
Scheme.affine_cover_ring _ i.2.2

def pullback_affine_cover_ring_base : CommRing :=
Scheme.affine_cover_ring _ i.1

@[derive is_open_immersion]
def pullback_affine_cover_map_left : 
  Scheme.Spec.obj (op $ pullback_affine_cover_ring_left f g i) ⟶ X :=
(pullback f (Z.affine_cover.map i.1)).affine_cover.map i.2.1 ≫ pullback.fst

@[derive is_open_immersion]
def pullback_affine_cover_map_right : 
  Scheme.Spec.obj (op $ pullback_affine_cover_ring_right f g i) ⟶ Y :=
(pullback g (Z.affine_cover.map i.1)).affine_cover.map i.2.2 ≫ pullback.fst

@[derive is_open_immersion]
def pullback_affine_cover_map_base : 
  Scheme.Spec.obj (op $ pullback_affine_cover_ring_base f g i) ⟶ Z :=
Z.affine_cover.map i.1

def pullback_affine_cover_map_fst : 
  Scheme.Spec.obj (op $ pullback_affine_cover_ring_left f g i) ⟶
    Scheme.Spec.obj (op $ pullback_affine_cover_ring_base f g i) :=
(pullback f (Z.affine_cover.map i.1)).affine_cover.map i.2.1 ≫ pullback.snd

def pullback_affine_cover_map_snd : 
  Scheme.Spec.obj (op $ pullback_affine_cover_ring_right f g i) ⟶
    Scheme.Spec.obj (op $ pullback_affine_cover_ring_base f g i) :=
(pullback g (Z.affine_cover.map i.1)).affine_cover.map i.2.2 ≫ pullback.snd

instance :
  algebra (pullback_affine_cover_ring_base f g i) (pullback_affine_cover_ring_left f g i) :=
(Scheme.Spec.preimage (pullback_affine_cover_map_fst f g i)).unop.to_algebra

instance :
  algebra (pullback_affine_cover_ring_base f g i) (pullback_affine_cover_ring_right f g i) :=
(Scheme.Spec.preimage (pullback_affine_cover_map_snd f g i)).unop.to_algebra

def pullback_affine_cover_ring : CommRing :=
CommRing.of $
  tensor_product (pullback_affine_cover_ring_base f g i) (pullback_affine_cover_ring_left f g i)
    (pullback_affine_cover_ring_right f g i)

instance pullback_affine_cover_ring.left_algebra :
  algebra (pullback_affine_cover_ring_left f g i) (pullback_affine_cover_ring f g i) :=
algebra.tensor_product.left_algebra

instance pullback_affine_cover_ring.right_algebra :
  algebra (pullback_affine_cover_ring_right f g i) (pullback_affine_cover_ring f g i) :=
ring_hom.to_algebra algebra.tensor_product.include_right.to_ring_hom

instance pullback_affine_cover_ring.algebra :
  algebra (pullback_affine_cover_ring_base f g i) (pullback_affine_cover_ring f g i) :=
algebra.tensor_product.left_algebra

instance pullback_affine_cover_ring.left_tower :
  is_scalar_tower (pullback_affine_cover_ring_base f g i)
    (pullback_affine_cover_ring_left f g i) (pullback_affine_cover_ring f g i) :=
algebra.tensor_product.tensor_product.is_scalar_tower

instance pullback_affine_cover_ring.right_tower :
  is_scalar_tower (pullback_affine_cover_ring_base f g i)
    (pullback_affine_cover_ring_right f g i) (pullback_affine_cover_ring f g i) :=
is_scalar_tower.of_algebra_map_eq' algebra.tensor_product.include_right.comp_algebra_map.symm

lemma pullback_affine_cover_obj :
  (pullback_affine_cover f g).obj i =
    pullback (pullback_affine_cover_map_fst f g i) (pullback_affine_cover_map_snd f g i) := rfl

def pullback_affine_cover_obj_iso :
  (pullback_affine_cover f g).obj i ≅ Scheme.Spec.obj (op $ pullback_affine_cover_ring f g i) :=
begin
  refine (as_iso $ pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) _ _) ≪≫ pullback_symmetry _ _ ≪≫
    limit.iso_limit_cone ⟨_, ((is_pushout.of_is_colimit (CommRing.pushout_cocone_is_colimit
    (Scheme.Spec.preimage (pullback_affine_cover_map_fst f g i)).unop
      (Scheme.Spec.preimage (pullback_affine_cover_map_snd f g i)).unop))
      .op.map Scheme.Spec).is_limit⟩,
  { simpa only [category.id_comp, quiver.hom.op_unop, functor.image_preimage, category.comp_id] },
  { simpa only [category.id_comp, quiver.hom.op_unop, functor.image_preimage, category.comp_id] },
  apply_instance
end

lemma pullback_affine_cover_obj_iso_inv_fst :
  (pullback_affine_cover_obj_iso f g i).inv ≫ pullback.fst = Scheme.Spec.map (quiver.hom.op $
    (algebra_map (pullback_affine_cover_ring_left f g i) (pullback_affine_cover_ring f g i) : _)) :=
begin
  rw iso.inv_comp_eq,
  simp only [pullback_affine_cover_obj_iso, iso.trans_hom, as_iso_hom, category.assoc],
  erw [limit.iso_limit_cone_hom_π ⟨_, ((is_pushout.of_is_colimit (CommRing.pushout_cocone_is_colimit
    (Scheme.Spec.preimage (pullback_affine_cover_map_fst f g i)).unop
      (Scheme.Spec.preimage (pullback_affine_cover_map_snd f g i)).unop))
      .op.map Scheme.Spec).is_limit⟩ walking_cospan.right, pullback_symmetry_hom_comp_snd],
  rw [pullback.lift_fst, category.comp_id],
end

lemma pullback_affine_cover_obj_iso_inv_snd :
  (pullback_affine_cover_obj_iso f g i).inv ≫ pullback.snd = Scheme.Spec.map (quiver.hom.op $
    (algebra_map (pullback_affine_cover_ring_right f g i) (pullback_affine_cover_ring f g i) : _)) :=
begin
  rw iso.inv_comp_eq,
  simp only [pullback_affine_cover_obj_iso, iso.trans_hom, as_iso_hom, category.assoc],
  erw [limit.iso_limit_cone_hom_π ⟨_, ((is_pushout.of_is_colimit (CommRing.pushout_cocone_is_colimit
    (Scheme.Spec.preimage (pullback_affine_cover_map_fst f g i)).unop
      (Scheme.Spec.preimage (pullback_affine_cover_map_snd f g i)).unop))
      .op.map Scheme.Spec).is_limit⟩ walking_cospan.left, pullback_symmetry_hom_comp_fst],
  rw [pullback.lift_snd, category.comp_id],
end

lemma pullback_affine_cover_map_fst_base :
  pullback_affine_cover_map_fst f g i ≫ pullback_affine_cover_map_base f g i =
    pullback_affine_cover_map_left f g i ≫ f := 
by simp only [category.assoc, pullback_affine_cover_map_base, pullback.condition,
      pullback_affine_cover_map_left, pullback_affine_cover_map_fst]

lemma pullback_affine_cover_map_snd_base :
  pullback_affine_cover_map_snd f g i ≫ pullback_affine_cover_map_base f g i =
    pullback_affine_cover_map_right f g i ≫ g := 
by simp only [category.assoc, pullback_affine_cover_map_base, pullback.condition,
      pullback_affine_cover_map_right, pullback_affine_cover_map_snd]

lemma pullback_affine_cover_map :
  (pullback_affine_cover f g).map i = 
    pullback.map (pullback_affine_cover_map_fst f g i) (pullback_affine_cover_map_snd f g i)
    f g (pullback_affine_cover_map_left f g i) (pullback_affine_cover_map_right f g i)
    (pullback_affine_cover_map_base f g i)
    (pullback_affine_cover_map_fst_base f g i)
    (pullback_affine_cover_map_snd_base f g i) :=
begin
  delta pullback_affine_cover,
  apply pullback.hom_ext; simp only [pullback_affine_cover_map_base, pullback_affine_cover_map_left,
    pullback_affine_cover_map_right, pullback.lift_fst, pullback.lift_snd,
    Scheme.open_cover.bind_map, category.assoc, Scheme.pullback.open_cover_of_left_right_map,
    Scheme.pullback.open_cover_of_base_map, pullback.lift_fst_assoc, pullback.lift_snd_assoc],
end
.

lemma pullback_affine_cover_f_exists (T : pullback.triplet f g) : 
  ∃ i : (pullback_affine_cover f g).J, T.1 ∈ (pullback_affine_cover_map_left f g i).opens_range ∧ 
    T.2 ∈ (pullback_affine_cover_map_right f g i).opens_range :=
begin
  let i := Z.affine_cover.f T.z,
  obtain ⟨x, hx⟩ : T.x ∈ (pullback.fst : pullback f (Z.affine_cover.map i) ⟶ _).opens_range,
  { rw [← opens.mem_coe, Scheme.hom.opens_range_coe, pullback.range_fst, set.mem_preimage,
      T.hx], exact Z.affine_cover.covers T.z },
  obtain ⟨y, hy⟩ : T.y ∈ (pullback.fst : pullback g (Z.affine_cover.map i) ⟶ _).opens_range,
  { rw [← opens.mem_coe, Scheme.hom.opens_range_coe, pullback.range_fst, set.mem_preimage,
      T.hy], exact Z.affine_cover.covers T.z },
  refine ⟨⟨i, x, y⟩, _, _⟩,
  { obtain ⟨x', hx'⟩ := (pullback f (Z.affine_cover.map i)).affine_cover.covers x,
    conv_lhs { rw [← hx, ← hx'] }, exact ⟨x', rfl⟩ },
  { obtain ⟨y', hy'⟩ := (pullback g (Z.affine_cover.map i)).affine_cover.covers y,
    conv_lhs { rw [← hy, ← hy'] }, exact ⟨y', rfl⟩ },
end

noncomputable!
def pullback_Top_open_cover : opens (types.pullback_obj f.1.base g.1.base) :=
⟨_, ⟨_, (pullback_affine_cover_map_left f g i).opens_range.prop.prod
  (pullback_affine_cover_map_right f g i).opens_range.prop, rfl⟩⟩  

lemma pullback_Top_open_cover_supr :
  supr (pullback_Top_open_cover f g) = ⊤ :=
begin
  rw eq_top_iff,
  rintro ⟨⟨x, y⟩, e⟩ -,
  obtain ⟨i, ⟨x', rfl : _ = x⟩, ⟨y', rfl : _ = y⟩⟩ :=
    pullback_affine_cover_f_exists _ _ (pullback.triplet_mk f g x y e),
  refine opens.mem_supr.mpr ⟨i, ⟨x', rfl⟩, ⟨y', rfl⟩⟩
end

noncomputable!
def pullback_Top_open_cover_preimage_homeo :
  pullback_comparison f g ⁻¹' (pullback_Top_open_cover f g i).1 ≃ₜ
    prime_spectrum (pullback_affine_cover_ring f g i) :=
begin
  have : pullback_comparison f g ⁻¹' (pullback_Top_open_cover f g i).1 =
    ((pullback_affine_cover f g).map i).opens_range,
  { ext x, simp only [pullback_affine_cover_map, set.mem_preimage, Scheme.hom.opens_range_coe,
      pullback.range_map], refl },
  exact ((homeomorph.set_congr this).trans (homeomorph.of_embedding _ (is_open_immersion.base_open
    ((pullback_affine_cover f g).map i)).to_embedding : _).symm).trans 
    (Top.homeo_of_iso $ Scheme.forget_to_Top.map_iso $ pullback_affine_cover_obj_iso f g i),
end

noncomputable!
def pullback_Top_open_cover_homeo :
  (pullback_Top_open_cover f g i).1 ≃ₜ types.pullback_obj
    (prime_spectrum.comap $ algebra_map
      (pullback_affine_cover_ring_base f g i) (pullback_affine_cover_ring_left f g i))
    (prime_spectrum.comap $ algebra_map
      (pullback_affine_cover_ring_base f g i) (pullback_affine_cover_ring_right f g i)) :=
begin
  refine (homeomorph.of_embedding _ $ embedding_subtype_coe.comp embedding_subtype_coe).trans
    ((homeomorph.set_congr _).trans (homeomorph.of_embedding _ $ 
    ((is_open_immersion.base_open (pullback_affine_cover_map_left f g i)).to_embedding.prod_mk
      (is_open_immersion.base_open (pullback_affine_cover_map_right f g i)).to_embedding).comp
      embedding_subtype_coe).symm),
    ext x, split, swap,
    { rintros ⟨⟨⟨x, y⟩, e⟩, rfl⟩,
      refine ⟨⟨⟨⟨_, _⟩, _⟩, ⟨x, rfl⟩, ⟨y, rfl⟩⟩, rfl⟩,
      change (pullback_affine_cover_map_left f g i ≫ f).1.base x = 
        (pullback_affine_cover_map_right f g i ≫ g).1.base y,
      simp only [ring_hom.algebra_map_to_algebra, ← Scheme.Spec_map_val_base,
        quiver.hom.op_unop, functor.image_preimage] at e,
      rw [← pullback_affine_cover_map_fst_base, ← pullback_affine_cover_map_snd_base,
        Scheme.comp_val_base_apply, Scheme.comp_val_base_apply, e] },
    { rintros ⟨⟨⟨⟨x', y'⟩, e⟩, ⟨x, (rfl : _ = x')⟩, ⟨y, (rfl : _ = y')⟩⟩, rfl⟩,
      refine ⟨⟨⟨x, y⟩, _⟩, rfl⟩,
      change (pullback_affine_cover_map_left f g i ≫ f).1.base x = 
        (pullback_affine_cover_map_right f g i ≫ g).1.base y at e,
      apply (is_open_immersion.base_open $ pullback_affine_cover_map_base f g i).inj,
      simp only [ring_hom.algebra_map_to_algebra, ← Scheme.Spec_map_val_base,
        quiver.hom.op_unop, functor.image_preimage, ← Scheme.comp_val_base_apply,
        pullback_affine_cover_map_fst_base, pullback_affine_cover_map_snd_base, e] }
end

lemma homeomorph.trans_symm_apply {α β γ : Type*} [topological_space α] [topological_space β]
  [topological_space γ] (h₁ : α ≃ₜ β) (h₂ : β ≃ₜ γ) (x) :
  (h₁.trans h₂).symm x = h₁.symm (h₂.symm x) := rfl

lemma homeomorph.symm_symm_apply {α β : Type*} [topological_space α] [topological_space β]
  (h : α ≃ₜ β) (x) : h.symm.symm x = h x := rfl 

lemma homeomorph.symm_apply_eq {α β : Type*} [topological_space α] [topological_space β]
  (h : α ≃ₜ β) {x y} : h.symm x = y ↔ x = h y := h.to_equiv.symm_apply_eq

lemma homeomorph.coe_set_congr_symm {α : Type*} [topological_space α] (s t : set α)
  (h : s = t) (x) : ((homeomorph.set_congr h).symm x : α) = x := rfl

lemma homeomorph.coe_of_embedding {α β : Type*} [topological_space α] [topological_space β]
  (f : α → β) (hf : embedding f) {x} : (homeomorph.of_embedding f hf x : β) = f x := rfl

lemma Scheme.forget_to_Top_map' {X Y : Scheme} (f : X ⟶ Y) :
  Scheme.forget_to_Top.map f = f.1.base := rfl

lemma pullback_comparison_restrict_pullback_Top_open_cover :
  (pullback_Top_open_cover f g i).1.restrict_preimage (pullback_comparison f g) = 
    (pullback_Top_open_cover_homeo f g i).symm ∘ prime_spectrum.tensor_product_to _ _ _ ∘
      pullback_Top_open_cover_preimage_homeo f g i :=
begin
  rw [eq_comm, ← (pullback_Top_open_cover_preimage_homeo f g i).coe_to_equiv, 
    ← function.comp.assoc, ← equiv.eq_comp_symm],
  ext x : 1,
  dsimp only [function.comp_apply, subtype.coe_mk,
    pullback_Top_open_cover_preimage_homeo, homeomorph.trans_apply,
      pullback_Top_open_cover_homeo, homeomorph.trans_apply, homeomorph.coe_symm_to_equiv,
      homeomorph.trans_symm_apply, homeomorph.symm_symm_apply],
  rw homeomorph.symm_apply_eq,
  ext1,
  dsimp only [functor.map_iso_inv, Top.homeo_of_iso_symm_apply, Scheme.forget_to_Top_map',
    homeomorph.coe_set_congr_symm, homeomorph.coe_of_embedding, function.comp_apply,
    set.restrict_preimage_coe, prime_spectrum.tensor_product_to_apply_coe_fst,
    prime_spectrum.tensor_product_to_apply_coe_snd],
  ext1,
  { simp only [pullback_comparison_apply_coe_fst, ← Scheme.comp_val_base_apply],
    convert_to (Scheme.Spec.map (quiver.hom.op $ algebra_map
      (pullback_affine_cover_ring_left f g i) (pullback_affine_cover_ring f g i)) ≫
        pullback_affine_cover_map_left f g i).1.base x = _,
    erw ← pullback_affine_cover_obj_iso_inv_fst,
    simp only [category.assoc, pullback_affine_cover_map, pullback.lift_fst] },
  { simp only [pullback_comparison_apply_coe_snd, ← Scheme.comp_val_base_apply],
    convert_to (Scheme.Spec.map (quiver.hom.op $ algebra_map
      (pullback_affine_cover_ring_right f g i) (pullback_affine_cover_ring f g i)) ≫
        pullback_affine_cover_map_right f g i).1.base x = _,
    erw ← pullback_affine_cover_obj_iso_inv_snd,
    simp only [category.assoc, pullback_affine_cover_map, pullback.lift_snd] },
end


end open_cover

instance {R : Type u} [comm_ring R] (x : prime_spectrum R) :
  epi (structure_sheaf.to_stalk R x) :=
begin
  constructor,
  intros Z g h e,
  exact is_localization.ring_hom_ext x.as_ideal.prime_compl e,
end

def _root_.CommRing.iso_of (R : CommRing) : R ≅ CommRing.of R :=
⟨ring_hom.id R, ring_hom.id R, rfl, rfl⟩

def Spec.stalk_map_iso {R S : CommRing.{u}} (f : R ⟶ S) (x) :
  arrow.mk (PresheafedSpace.stalk_map (Scheme.Spec.map f.op).val x) ≅ 
  arrow.mk (CommRing.of_hom $ localization.at_prime.map f x.as_ideal) :=
begin
  refine arrow.iso_mk' _ _ (structure_sheaf.stalk_iso R (prime_spectrum.comap f x))
    (structure_sheaf.stalk_iso S x) _,
  rw ← cancel_epi (structure_sheaf.to_stalk R (prime_spectrum.comap f x)),
  rw [structure_sheaf.stalk_iso_hom, ← category.assoc, 
    structure_sheaf.to_stalk_comp_stalk_to_fiber_ring_hom, structure_sheaf.to_stalk,
    category.assoc],
  erw [PresheafedSpace.stalk_map_germ'_assoc (Scheme.Spec.map f.op).1 x,
    ← Spec_Γ_naturality'_assoc f, ← category.assoc (to_Spec_Γ S),
    structure_sheaf.to_stalk_comp_stalk_to_fiber_ring_hom],
  convert_to (localization.at_prime.map f x.as_ideal).comp
    (algebra_map R (localization (prime_spectrum.comap f x).as_ideal.prime_compl)) = 
    (algebra_map S (localization (@prime_spectrum.as_ideal S _ x).prime_compl)).comp f,
  exact is_localization.map_comp _
end
.

lemma surjective_on_stalks_iff {R S : CommRing.{u}} (f : R ⟶ S) :
  f.surjective_on_stalks ↔
    ∀ x, function.surjective (PresheafedSpace.stalk_map (Scheme.Spec.map f.op).1 x) :=
begin
  delta ring_hom.surjective_on_stalks,
  have := λ x, (morphism_property.surjective_respects_iso CommRing).arrow_mk_iso_iff
    (Spec.stalk_map_iso f x),
  dsimp only [morphism_property.surjective] at this, simp_rw this,
  exact ⟨λ H x, H x.as_ideal, λ H x hx, H ⟨x, hx⟩⟩
end

lemma Scheme.open_cover.exists_covers {X : Scheme} (𝒰 : X.open_cover) (x : X.carrier) :
  ∃ i (y : (𝒰.obj i).carrier), (𝒰.map i).1.base y = x :=
⟨_, 𝒰.covers x⟩

lemma Scheme.comp_val' {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g).1 = @category_struct.comp (PresheafedSpace.{u} CommRing.{u}) _ _ _ _ f.1 g.1 := rfl

include hg

lemma pullback_snd_surjective_on_stalks (x) : function.surjective
  (PresheafedSpace.stalk_map (pullback.fst : pullback f g ⟶ _).1 x) :=
begin
  obtain ⟨i, y, rfl⟩ := (pullback_affine_cover f g).exists_covers x,
  refine ((morphism_property.surjective_respects_iso CommRing).cancel_right_is_iso _
    (PresheafedSpace.stalk_map ((pullback_affine_cover f g).map i).1 _)).mp _,
  rw ← PresheafedSpace.stalk_map.comp,
  change morphism_property.surjective _ (PresheafedSpace.stalk_map
    ((pullback_affine_cover f g).map i ≫ pullback.fst).1 y),
  rw [pullback_affine_cover_map, pullback.lift_fst, Scheme.comp_val',
    PresheafedSpace.stalk_map.comp,
    (morphism_property.surjective_respects_iso CommRing).cancel_left_is_iso,
    ← (pullback_affine_cover_obj_iso f g i).hom_inv_id_assoc pullback.fst,
    pullback_affine_cover_obj_iso_inv_fst, Scheme.comp_val',
    PresheafedSpace.stalk_map.comp,
    (morphism_property.surjective_respects_iso CommRing).cancel_right_is_iso],
  erw (morphism_property.surjective_respects_iso CommRing).arrow_mk_iso_iff
    (Spec.stalk_map_iso _ _),
  convert tensor_product_surjective_on_stalks
    (pullback_affine_cover_ring_base f g i) (pullback_affine_cover_ring_left f g i)
    (pullback_affine_cover_ring_right f g i) _
    (((pullback_affine_cover_obj_iso f g i).hom.1.base) y).as_ideal,
  intros x hx,
  refine ((morphism_property.surjective_respects_iso CommRing).arrow_mk_iso_iff
    (Spec.stalk_map_iso _ ⟨x, hx⟩)).mp _,
  rw [ring_hom.algebra_map_to_algebra, quiver.hom.op_unop, functor.image_preimage],
  refine ((morphism_property.surjective_respects_iso CommRing).cancel_left_is_iso
    (PresheafedSpace.stalk_map (pullback_affine_cover_map_base f g i).1 _) _).mp _,
  rw ← PresheafedSpace.stalk_map.comp,
  change morphism_property.surjective _ (PresheafedSpace.stalk_map
    (pullback_affine_cover_map_snd f g i ≫ pullback_affine_cover_map_base f g i).1 _),
  rw [pullback_affine_cover_map_snd_base, Scheme.comp_val', PresheafedSpace.stalk_map.comp,
    (morphism_property.surjective_respects_iso CommRing).cancel_right_is_iso],
  exact hg _,
end

lemma embedding_pullback_comparison_of_surjective_on_stalks : 
  embedding (pullback_comparison f g) :=
begin
  refine (embedding_iff_embedding_of_supr_eq_top (pullback_Top_open_cover_supr f g)
    (pullback_comparison f g).2).mpr (λ i, _), 
  erw pullback_comparison_restrict_pullback_Top_open_cover,
  refine (homeomorph.embedding _).comp (embedding.comp _ $ homeomorph.embedding _),
  apply prime_spectrum.tensor_product_to_embedding,
  rw surjective_on_stalks_iff,
  intro x,
  rw [ring_hom.algebra_map_to_algebra, quiver.hom.op_unop, functor.image_preimage,
    pullback_affine_cover_map_snd],
  refine ((morphism_property.surjective_respects_iso CommRing).cancel_left_is_iso
    (PresheafedSpace.stalk_map (Z.affine_cover.map i.fst).1 _) _).mp _,
  rw ← PresheafedSpace.stalk_map.comp,
  convert_to function.surjective
    (PresheafedSpace.stalk_map ((_ ≫ pullback.snd) ≫ Z.affine_cover.map i.1).1 x),
  rw [category.assoc, ← pullback.condition, ← category.assoc, Scheme.comp_val],
  erw PresheafedSpace.stalk_map.comp,
  exact (as_iso $ PresheafedSpace.stalk_map ((pullback g (Z.affine_cover.map i.1)).affine_cover.map
    i.2.2 ≫ pullback.fst).1 x).CommRing_iso_to_ring_equiv.surjective.comp (hg _),
end

lemma embedding_category_theory_pullback_comparison_of_surjective_on_stalks : 
  embedding (category_theory.limits.pullback_comparison Scheme.forget_to_Top f g) :=
begin
  rw ← pullback_comparison_comp_pullback_iso_prod_subtype_inv,
  exact (Top.homeo_of_iso (Top.pullback_iso_prod_subtype f.val.base g.val.base).symm)
    .embedding.comp (embedding_pullback_comparison_of_surjective_on_stalks f g hg),
end

end algebraic_geometry