import morphisms.closed_immersion
import for_mathlib.field
import topology.local_at_target

open opposite category_theory category_theory.limits topological_space

noncomputable theory

namespace algebraic_geometry

section fiber

universe u

variables {X Y : Scheme.{u}}

abbreviation Scheme.stalk_residue (X : Scheme) (x : X.carrier) :
  X.stalk x ⟶ X.residue_field x :=
local_ring.residue _ 

lemma is_iso_to_stalk_residue {R : Type*} [field R] (x) : 
  is_iso (structure_sheaf.to_stalk R x ≫ (Scheme.Spec.obj $ op $ CommRing.of R).stalk_residue _) :=
begin
  apply_with (is_iso_of_reflects_iso _ (forget $ CommRing)) { instances := ff },
  rw is_iso_iff_bijective,
  refine ⟨ring_hom.injective _, _⟩,
  intro y,
  obtain ⟨y' : (Spec.structure_sheaf R).presheaf.stalk x, rfl⟩ := ideal.quotient.mk_surjective y,
  obtain ⟨y : R, s, rfl⟩ := is_localization.mk'_surjective x.as_ideal.prime_compl y',
  have : (s : R) ≠ 0 := λ e, s.prop (e.symm ▸ x.as_ideal.zero_mem),
  refine ⟨(y/s : _), _⟩,
  change ideal.quotient.mk _ _ = _,
  congr' 1,
  apply is_localization.eq_mk'_iff_mul_eq.mpr,
  refine ((map_mul _ _ _).symm.trans _),
  rw div_mul_cancel _ this,
  refl
end
.
instance (X : Scheme) (x) : epi (X.stalk_residue x) :=
begin
  refine (forget _).epi_of_epi_map _,
  rw epi_iff_surjective,
  exact ideal.quotient.mk_surjective
end

@[simp, reassoc]
lemma Scheme.stalk_residue_eq (X : Scheme) {x y : X.carrier} (e : x = y) : 
  X.stalk_residue y ≫ X.residue_field_of_eq e =
    X.presheaf.stalk_specializes (specializes_of_eq e) ≫ X.stalk_residue x := rfl

@[simp, reassoc]
lemma Scheme.stalk_residue_map {X Y : Scheme} (f : X ⟶ Y) {x : X.carrier} : 
  Y.stalk_residue _ ≫ f.map_residue_field x = PresheafedSpace.stalk_map f.1 x ≫ X.stalk_residue x :=
rfl

lemma is_affine.hom_ext {X Y : Scheme} [is_affine Y] (f g : X ⟶ Y) (e : Scheme.Γ.map f.op = Scheme.Γ.map g.op) :
  f = g :=
begin
  rw [← cancel_mono (Γ_Spec.adjunction.unit.app Y), ← Γ_Spec.adjunction.unit_naturality f, ← Γ_Spec.adjunction.unit_naturality g,
    functor.right_op_map, functor.right_op_map, e],
end

lemma is_affine_open.from_Spec_of_affine {R : CommRing} {U : opens (Scheme.Spec.obj $ op R).carrier} (h : is_affine_open U) :
  h.from_Spec = Scheme.Spec.map (eq_to_hom (by unfreezingI { cases R, refl }) ≫ structure_sheaf.to_open R U).op :=
begin
  apply is_affine.hom_ext,
  delta is_affine_open.from_Spec Scheme.iso_Spec,
  haveI : is_affine _ := h,
  have := @adjunction.left_triangle_components _ _ _ _ _ _ Γ_Spec.adjunction ((Scheme.Spec.obj (op R)).restrict U.open_embedding),
  rw [functor.right_op_map, ← quiver.hom.unop_inj.eq_iff, unop_comp, quiver.hom.unop_op] at this,
  have := is_iso.eq_inv_of_inv_hom_id this,
  apply quiver.hom.op_inj,
  simp only [quiver.hom.op_unop, functor.map_inv, op_inv, as_iso_inv, op_comp, category.assoc, functor.map_comp, unop_comp, ← this],
  erw Γ_Spec.adjunction.counit_naturality_assoc,
  rw [← is_iso.comp_inv_eq, ← cancel_mono (Γ_Spec.adjunction.counit.app $ op $ CommRing.of R)],
  conv_rhs { erw (Γ_Spec.adjunction.counit_naturality (structure_sheaf.to_open R U).op) },
  simp_rw [category.assoc],
  congr' 1,
  unfreezingI { cases R },
  slice_lhs 3 3 { simp only [eq_to_hom_op, eq_to_hom_map Scheme.Spec, eq_to_hom_map Scheme.Γ, inv_eq_to_hom] },
  apply quiver.hom.unop_inj,
  simp only [algebraic_geometry.Γ_Spec.LocallyRingedSpace_adjunction_counit, nat_trans.op_app, quiver.hom.unop_op,
    unop_inv, Scheme.Spec_map_2, Scheme.Γ_map, Spec_Γ_identity_inv_app, category.assoc,
    Γ_Spec.adjunction_counit_app, unop_comp, eq_to_hom_refl, to_Spec_Γ, is_iso.inv_id],
  dsimp,
  rw [category.id_comp, reassoc_of structure_sheaf.to_open_res, structure_sheaf.to_open_res]
end

@[elementwise, reassoc]
lemma Scheme.from_Spec_residue_field_map_residue_field {X : Scheme} (x) (s)  : 
  X.residue_field_of_eq (Scheme.from_Spec_residue_field_base _ _)  ≫ 
    (X.from_Spec_residue_field x).map_residue_field s = structure_sheaf.to_stalk _ s ≫
    (Scheme.Spec.obj _).stalk_residue _ :=
begin
  apply quiver.hom.op_inj,
  apply Scheme.Spec.map_injective,
  rw [pullback.triplet.eq_from_Spec_residue_field_aux, Scheme.from_Spec_residue_field, op_comp, functor.map_comp],
  congr' 1,
  rw [← (top_is_affine_open _).from_Spec_stalk_eq],
  rotate, { trivial }, { apply_instance },
  delta is_affine_open.from_Spec_stalk structure_sheaf.to_stalk,
  rw [op_comp, functor.map_comp, is_affine_open.from_Spec_of_affine],
  refl
end

@[instance]
lemma is_iso_from_Spec_residue_field_map_residue {X : Scheme} (x) (s) :
  is_iso ((X.from_Spec_residue_field x).map_residue_field s) :=
begin
  apply_with (is_iso_of_reflects_iso _ (forget $ CommRing)) { instances := ff },
  rw is_iso_iff_bijective,
  refine ⟨ring_hom.injective _, _⟩,
  intro y,
  obtain ⟨y' : (Spec.structure_sheaf _).presheaf.stalk s, rfl⟩ := ideal.quotient.mk_surjective y,
  obtain ⟨y, rfl⟩ : ∃ y : X.residue_field x, structure_sheaf.to_stalk _ s y = y',
  { obtain ⟨y : X.residue_field x, t, rfl⟩ := is_localization.mk'_surjective s.as_ideal.prime_compl y',
    refine ⟨y/t.1, _⟩,
    apply is_localization.eq_mk'_iff_mul_eq.mpr,
    refine (map_mul _ _ _).symm.trans _,
    rw [subtype.val_eq_coe, div_mul_cancel],
    exacts [rfl, λ e, t.prop (e.symm ▸ s.as_ideal.zero_mem)] },
  refine ⟨X.residue_field_of_eq (Scheme.from_Spec_residue_field_base _ _) y, _⟩,
  refine (Scheme.from_Spec_residue_field_map_residue_field_apply x s y).trans _,
  refl
end

instance {X : Scheme} {x y} (e : x = y) : is_iso (X.residue_field_of_eq e) :=
⟨⟨X.residue_field_of_eq e.symm, by simp, by simp⟩⟩

def Scheme.hom.fiber (f : X ⟶ Y) (y : Y.carrier) : Scheme :=
pullback f (Y.from_Spec_residue_field y)

@[derive is_preimmersion]
def Scheme.hom.fiber_ι (f : X ⟶ Y) (y : Y.carrier) : f.fiber y ⟶ X :=
pullback.fst

def Scheme.hom.fiber_to_residue_field (f : X ⟶ Y) (y : Y.carrier) :
  f.fiber y ⟶ Scheme.Spec.obj (op $ Y.residue_field y) :=
pullback.snd

def Scheme.hom.fiber_residue_field_tensor_iso (f : X ⟶ Y) (y : Y.carrier)
  (T : pullback.triplet f (Y.from_Spec_residue_field y)) : 
  T.residue_field_tensor ≅ X.residue_field T.x :=
(as_iso pushout.inl).symm

instance (f : X ⟶ Y) (y : Y.carrier)
  (T : pullback.triplet f (Y.from_Spec_residue_field y)) : 
  field T.residue_field_tensor :=
(f.fiber_residue_field_tensor_iso y T).CommRing_iso_to_ring_equiv.symm.is_field.to_field

def Scheme.hom.fiber_carrier (f : X ⟶ Y) (y : Y.carrier) :
  (f.fiber y).carrier ≃ₜ { x : X.carrier // f.1.base x = y } :=
begin
  refine (homeomorph.of_embedding _ (is_preimmersion.base_embedding $ f.fiber_ι y)).trans
    (homeomorph.set_congr _),
  ext x,
  rw [Scheme.hom.fiber_ι, pullback.range_fst, Scheme.range_from_Spec_residue_field],
  exact set.mem_singleton_iff
end 

@[simp]
lemma Scheme.hom.fiber_carrier_apply (f : X ⟶ Y) (y : Y.carrier) (x) :
  (f.fiber_carrier y x : X.carrier) = (f.fiber_ι y).1.base x := rfl

lemma Scheme.hom.fiber_ι_coe (f : X ⟶ Y) (y : Y.carrier) :
  ⇑(f.fiber_ι y).1.base = (coe ∘ (f.fiber_carrier y) : _ → X.carrier) :=
funext $ λ x, (f.fiber_carrier_apply y x).symm

lemma Scheme.hom.range_fiber_ι (f : X ⟶ Y) (y : Y.carrier) :
  set.range (f.fiber_ι y).1.base = f.1.base ⁻¹' {y} :=
begin
  rw [Scheme.hom.fiber_ι_coe, set.range_comp, set.range_iff_surjective.mpr
    (f.fiber_carrier y).surjective, set.image_univ, subtype.range_coe],
  ext, rw [set.mem_preimage, set.mem_singleton_iff], refl,
end

def Scheme.hom.Spec_residue_field_to_fiber (f : X ⟶ Y) (x : X.carrier) : 
  Scheme.Spec.obj (op $ X.residue_field x) ⟶ f.fiber (f.1.base x) :=
pullback.lift _ _ (f.map_residue_field_from_Spec_residue_field x).symm

@[simp, reassoc]
lemma Scheme.hom.Spec_residue_field_to_fiber_ι (f : X ⟶ Y) (x : X.carrier) : 
  f.Spec_residue_field_to_fiber x ≫ f.fiber_ι _ = X.from_Spec_residue_field x :=
pullback.lift_fst _ _ _

@[simp, reassoc]
lemma Scheme.hom.Spec_residue_field_to_fiber_to_residue_field (f : X ⟶ Y) (x : X.carrier) : 
  f.Spec_residue_field_to_fiber x ≫ f.fiber_to_residue_field _ =
    Scheme.Spec.map (f.map_residue_field x).op :=
pullback.lift_snd _ _ _

instance (f : X ⟶ Y) (x : X.carrier) : is_preimmersion (f.Spec_residue_field_to_fiber x) :=
begin
  haveI H : is_preimmersion (X.from_Spec_residue_field x) := infer_instance,
  rw ← f.Spec_residue_field_to_fiber_ι at H,
  exact @@is_preimmersion.of_comp _ _ H
end

end fiber

end algebraic_geometry
