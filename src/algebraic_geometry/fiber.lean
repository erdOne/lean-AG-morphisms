import .points

namespace algebraic_geometry

section fiber

universe u

variables {X Y : Scheme.{u}}

abbreviation Scheme.stalk_residue (X : Scheme) (x : X.carrier) :
  X.stalk x ⟶ X.residue_field x :=
local_ring.residue _ 

lemma to_affine_residue_field {R : Type*} [field R] (x) : 
  is_iso (structure_sheaf.to_stalk R x ≫ (Scheme.Spec.obj $ op $ CommRing.of R).stalk_residue _) :=
begin
  apply_with (is_iso_of_reflects_iso _ (forget $ CommRing)) { instances := ff },
  rw is_iso_iff_bijective,
  refine ⟨ring_hom.injective _, _⟩,
  intro y,
  obtain ⟨y : (Spec.structure_sheaf R).presheaf.stalk x, rfl⟩ := ideal.quotient.mk_surjective y,
  obtain xx := is_localization.surj x.as_ideal.prime_compl y,

end

def Scheme.hom.fiber (f : X ⟶ Y) (y : Y.carrier) : Scheme :=
pullback f (Y.from_Spec_residue_field y)

def Scheme.hom.fiber_ι (f : X ⟶ Y) (y : Y.carrier) : f.fiber y ⟶ X :=
pullback.fst

def Scheme.hom.fiber_to_residue_field (f : X ⟶ Y) (y : Y.carrier) :
  f.fiber y ⟶ Scheme.Spec.obj (op $ Y.residue_field y) :=
pullback.snd

def Scheme.hom.fiber_carrier (f : X ⟶ Y) (y : Y.carrier) :
 (f.fiber y).carrier ≃ { x // f.1.base x = y } :=
begin
  refine (pullback.carrier_equiv _ _).trans _,
  refine
  { to_fun := λ h,
      ⟨h.1.x, h.1.hx.trans (h.1.hy.symm.trans $ Scheme.from_Spec_residue_field_base _ _)⟩,
    inv_fun := λ x, ⟨⟨x.1, show prime_spectrum (Y.residue_field y),
      from ⊥, _, x.2, Scheme.from_Spec_residue_field_base _ _⟩, _⟩,
    left_inv := _,
    right_inv := _ },
    dsimp only [pullback.triplet.residue_field_tensor],
end

end fiber

end algebraic_geometry
