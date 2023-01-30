import algebraic_geometry.pullbacks
import algebraic_geometry.AffineScheme
import linear_algebra.tensor_product_basis
import algebraic_geometry.misc


open opposite topological_space category_theory category_theory.limits

open local_ring (closed_point)

namespace algebraic_geometry

universe u

noncomputable theory

section local_ring_to_Scheme

variables {R : CommRing.{u}} [local_ring R] (X : Scheme.{u}) (f : Scheme.Spec.obj (op R) ⟶ X)

lemma CommRing.of_eq (R : CommRing) : CommRing.of R = R :=
by { cases R, refl }

lemma is_localization.at_prime.comap_maximal_ideal {R : Type*} (S : Type*) [comm_ring R] [comm_ring S]
  (I : ideal R) [I.is_prime] [algebra R S] [is_localization.at_prime S I] [local_ring S] :
  (local_ring.maximal_ideal S).comap (algebra_map R S) = I :=
ideal.ext $ λ x, by
simpa only [ideal.mem_comap] using is_localization.at_prime.to_map_mem_maximal_iff _ I x

lemma local_ring.specializes_closed_point {R : Type*} [comm_ring R] [local_ring R]
  (x : prime_spectrum R) :
  x ⤳ closed_point R :=
begin
  rw ← prime_spectrum.le_iff_specializes,
  exact local_ring.le_maximal_ideal x.2.1,
end

lemma local_ring.closed_point_mem_iff {R : Type*} [comm_ring R] [local_ring R]
  (U : opens $ prime_spectrum R) :
  closed_point R ∈ U ↔ U = ⊤ :=
begin
  split,
  { rw eq_top_iff, exact λ h x _, (local_ring.specializes_closed_point x).mem_open U.2 h },
  { rintro rfl, trivial }
end

lemma _root_.ring.is_field_iff_forall_ideal_eq {R : Type*} [comm_ring R] [nontrivial R] :
  is_field R ↔ ∀ I : ideal R, I = ⊥ ∨ I = ⊤ :=
begin
  rw [← not_iff_not, ring.not_is_field_iff_exists_ideal_bot_lt_and_lt_top],
  push_neg,
  simp_rw [lt_top_iff_ne_top, bot_lt_iff_ne_bot],
end

lemma field.ideal_eq {R : Type*} [field R] (I : ideal R) :
  I = ⊥ ∨ I = ⊤ :=
ring.is_field_iff_forall_ideal_eq.mp (field.to_is_field R) I

lemma _root_.local_ring.is_field_iff_maximal_ideal_eq {R : Type*} [comm_ring R] [local_ring R] :
  is_field R ↔ local_ring.maximal_ideal R = ⊥ :=
begin
  simp_rw [ring.is_field_iff_forall_ideal_eq, or_iff_not_imp_right],
  exact ⟨λ H, H (local_ring.maximal_ideal R) (ideal.is_prime.ne_top infer_instance),
    λ e I hI, eq_bot_iff.mpr (e ▸ local_ring.le_maximal_ideal hI)⟩,
end

instance {R : Type*} [comm_ring R] [is_domain R] : order_bot (prime_spectrum R) :=
{ bot := ⟨⊥, ideal.bot_prime⟩, bot_le := λ I, @bot_le _ _ _ I.as_ideal }

instance {R : Type*} [field R] : unique (prime_spectrum R) :=
{ default := ⊥,
  uniq := λ x, subtype.ext
    ((field.ideal_eq x.as_ideal).resolve_right (ideal.is_prime.ne_top infer_instance)) }

lemma _root_.prime_spectrum.comap_residue {R : Type*} [comm_ring R] [local_ring R]
  (I : prime_spectrum (local_ring.residue_field R)) :
  prime_spectrum.comap (local_ring.residue R) I = local_ring.closed_point R :=
begin
  have : I = ⊥ := subsingleton.elim _ _,
  subst this,
  ext1,
  exact ideal.mk_ker,
end

lemma local_ring.maximal_ideal_eq_bot {R : Type*} [field R] : local_ring.maximal_ideal R = ⊥ :=
local_ring.is_field_iff_maximal_ideal_eq.mp (field.to_is_field R)

def local_ring.lift_residue_field {R S : Type*} [comm_ring R] [local_ring R] [field S]
  (f : R →+* S) [is_local_ring_hom f] : local_ring.residue_field R →+* S :=
ideal.quotient.lift _ f (λ a ha,
  classical.by_contradiction (λ h, ha (is_unit_of_map_unit f a (is_unit_iff_ne_zero.mpr h))))

lemma local_ring.lift_residue_field_comp {R S : Type*} [comm_ring R] [local_ring R] [field S]
  (f : R →+* S) [is_local_ring_hom f] : local_ring.residue_field R →+* S :=
ideal.quotient.lift _ f (λ a ha,
  classical.by_contradiction (λ h, ha (is_unit_of_map_unit f a (is_unit_iff_ne_zero.mpr h))))

instance {R S : Type*} [field R] [comm_ring S] [nontrivial S] (f : R →+* S) :
  is_local_ring_hom f :=
⟨λ a ha, is_unit_iff_ne_zero.mpr (λ e, @not_is_unit_zero S _ _ $ by rwa [← map_zero f, ← e])⟩

instance {R : Type*} [comm_ring R] [local_ring R] :
  is_local_ring_hom (local_ring.residue R) :=
⟨λ a ha, not_not.mp (ideal.quotient.eq_zero_iff_mem.not.mp (is_unit_iff_ne_zero.mp ha))⟩

open topological_space

variables {X}

lemma is_affine_open.map_from_Spec {U V : opens X.carrier} (h : op U ⟶ op V)
  (hU : is_affine_open U) (hV : is_affine_open V) :
  Scheme.Spec.map (X.presheaf.map h).op ≫ hU.from_Spec = hV.from_Spec :=
begin
  delta is_affine_open.from_Spec Scheme.iso_Spec,
  rw ← is_iso.inv_comp_eq,
  rw iso.eq_inv_comp,
  simp only [← functor.map_inv, ← op_inv, eq_to_hom_op, inv_eq_to_hom,
    ← functor.map_comp_assoc, ← op_comp, ← functor.map_comp],
  rw [as_iso_hom, as_iso_inv, ← category.assoc],
  have e := (Γ_Spec.adjunction.unit.naturality (X.restrict_functor.map h.unop).1),
  rw [functor.id_map, category_theory.functor.comp_map, functor.right_op_map,
    Scheme.Γ_map_op, X.restrict_functor_map_app] at e,
  dsimp only [Scheme.restrict_functor, unop_op, over.mk, costructured_arrow.mk] at e,
  erw ← e,
  rw [category.assoc, is_iso.hom_inv_id_assoc, over.hom_mk_left, is_open_immersion.lift_fac],
end

def is_affine_open.from_Spec_stalk {U : opens X.carrier} (hU : is_affine_open U) {x : X.carrier}
  (hxU : x ∈ U) :
  Scheme.Spec.obj (op $ X.presheaf.stalk x) ⟶ X :=
Scheme.Spec.map (X.presheaf.germ ⟨x, hxU⟩).op ≫ hU.from_Spec

lemma from_Spec_stalk_eq (x : X.carrier) {U V : opens X.carrier}
  (hU : is_affine_open U) (hV : is_affine_open V) (hxU : x ∈ U) (hxV : x ∈ V) :
    hU.from_Spec_stalk hxU = hV.from_Spec_stalk hxV :=
begin
  obtain ⟨U', h₁, h₂, h₃ : U' ≤ U ⊓ V⟩ :=
    opens.is_basis_iff_nbhd.mp (is_basis_affine_open X) (show x ∈ U ⊓ V, from ⟨hxU, hxV⟩),
  transitivity h₁.from_Spec_stalk h₂; delta is_affine_open.from_Spec_stalk,
  { rw [← hU.map_from_Spec (hom_of_le $ h₃.trans inf_le_left).op h₁, ← functor.map_comp_assoc,
      ← op_comp, Top.presheaf.germ_res], refl },
  { rw [← hV.map_from_Spec (hom_of_le $ h₃.trans inf_le_right).op h₁, ← functor.map_comp_assoc,
      ← op_comp, Top.presheaf.germ_res], refl },
end

def Scheme.from_Spec_stalk (X : Scheme) (x : X.carrier) :
  Scheme.Spec.obj (op $ X.presheaf.stalk x) ⟶ X :=
(range_is_affine_open_of_open_immersion $ X.affine_cover.map x).from_Spec_stalk
  (X.affine_cover.covers x)

lemma is_affine_open.from_Spec_stalk_eq {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U)
  (x ∈ U) :
  hU.from_Spec_stalk H = X.from_Spec_stalk x :=
from_Spec_stalk_eq _ _ _ _ _

@[instance]
lemma Scheme.mono_from_Spec_stalk {X : Scheme} (x : X.carrier) : mono (X.from_Spec_stalk x) :=
begin
  apply_with mono_comp { instances := ff },
  swap, { apply_instance },
  apply_with functor.map_mono { instances := ff },
  { apply_instance },
  apply_with category_theory.op_mono_of_epi { instances := ff },
  have := (range_is_affine_open_of_open_immersion (X.affine_cover.map x)).is_localization_stalk
      ⟨x, X.affine_cover.covers x⟩,
  convert @is_localization.epi _ _ _ _ _ _ this,
  { exact (CommRing.of_eq _).symm },
  { exact (CommRing.of_eq _).symm }
end

lemma is_affine_open.from_Spec_stalk_closed_point {U : opens X.carrier} (hU : is_affine_open U)
  {x : X.carrier} (hxU : x ∈ U) :
  (hU.from_Spec_stalk hxU).1.base (closed_point (X.presheaf.stalk x) : _) = x :=
begin
  letI : is_affine _ := hU,
  rw [is_affine_open.from_Spec_stalk, is_affine_open.from_Spec, ← functor.map_comp_assoc,
    ← op_comp, Top.presheaf.germ_res],
  simp only [Top.comp_app, Scheme.of_restrict_val_base,
    quiver.hom.unop_op, Scheme.comp_coe_base, Scheme.Spec_map_2,
    eq_to_hom_op, opens.inclusion_apply],
  refine eq.trans _ (subtype.coe_mk x hxU),
  congr' 1,
  have : function.injective (X.restrict U.open_embedding).iso_Spec.hom.val.base,
  { rw ← Top.mono_iff_injective, apply_instance },
  apply this,
  convert_to ((X.restrict _).iso_Spec.inv ≫ (X.restrict _).iso_Spec.hom).val.base _ = _,
  rw [iso.inv_hom_id, Scheme.id_val_base, id_apply, Scheme.iso_Spec,
    as_iso_hom, Γ_Spec.adjunction_unit_app_base_apply, LocallyRingedSpace.Γ_to_stalk],
  erw [← PresheafedSpace.restrict_stalk_iso_inv_eq_germ, prime_spectrum.comap_comp],
  rw [continuous_map.comp_apply, local_ring.comap_closed_point],
  refl
end

lemma Scheme.from_Spec_stalk_closed_point (x : X.carrier) :
  (X.from_Spec_stalk x).1.base (closed_point (X.presheaf.stalk x) : _) = x :=
is_affine_open.from_Spec_stalk_closed_point _ _

lemma Scheme.range_from_Spec_stalk (X : Scheme) (x : X.carrier) :
  set.range (X.from_Spec_stalk x).1.base = { y | y ⤳ x } :=
begin
  apply le_antisymm,
  { rintros _ ⟨y, rfl⟩,
    dsimp at y,
    change _ ⤳ x,
    convert (local_ring.specializes_closed_point y).map (X.from_Spec_stalk x).1.base.2,
    exact (Scheme.from_Spec_stalk_closed_point x).symm },
  { rintros y (h : y ⤳ x),
    have h' := h,
    conv_rhs at h { rw ← Scheme.from_Spec_stalk_closed_point x },
    rw [Scheme.from_Spec_stalk, is_affine_open.from_Spec_stalk, Scheme.comp_val_base] at h ⊢,
    generalize_proofs _ _ hx hU,
    change x ∈ (X.affine_cover.map x).opens_range at hx,
    have hyU : y ∈ ((X.affine_cover.map x).opens_range : set X.carrier) :=
      h'.mem_open ((X.affine_cover.map x).opens_range.2) (X.affine_cover.covers x),
    rw [← hU.from_Spec_range] at hyU,
    obtain ⟨y', rfl⟩ := hyU,
    rw [coe_comp, set.range_comp],
    apply set.mem_image_of_mem,
    replace h := PresheafedSpace.is_open_immersion.base_open.to_inducing.specializes_iff.mp h,
    rw ← prime_spectrum.le_iff_specializes at h,
    haveI H := hU.is_localization_stalk ⟨x, hx⟩,
    erw @@prime_spectrum.localization_comap_range _ _ _ _ _ H,
    dsimp,
    apply set.subset_compl_iff_disjoint_left.mp,
    erw compl_compl,
    change y'.as_ideal ≤ (hU.prime_ideal_of ⟨x, hx⟩).as_ideal,
    convert h,
    ext1,
    exact (@@is_localization.at_prime.comap_maximal_ideal _ _ _ _ _ _ H _).symm }
end

def stalk_closed_point_to (R : CommRing) [local_ring R]
  (f : Scheme.Spec.obj (op R) ⟶ X) :
  X.presheaf.stalk (f.1.base (closed_point R : _)) ⟶ R :=
PresheafedSpace.stalk_map f.1 (closed_point R : _) ≫
  structure_sheaf.stalk_to_fiber_ring_hom R _ ≫
begin
  refine (@ring_equiv.to_CommRing_iso R
    (localization.at_prime (closed_point R).as_ideal) _ _ _).inv,
  refine (is_localization.at_units _
    (closed_point R).as_ideal.prime_compl _ _).to_ring_equiv,
  exact λ x, not_not.mp x.2,
end

instance (R : CommRing) [local_ring R]
  (f : Scheme.Spec.obj (op R) ⟶ X) : is_local_ring_hom (stalk_closed_point_to R f) :=
is_local_ring_hom_comp _ _

lemma structure_sheaf.is_iso_to_open_of_closed_point_mem (R : CommRing) [local_ring R]
  (f : Scheme.Spec.obj (op R) ⟶ X)
  (U : opens X.carrier) (hU : f.1.base (closed_point R : _) ∈ U) :
  is_iso (structure_sheaf.to_open R ((opens.map f.val.base).obj U)) :=
begin
  have : (opens.map f.val.base).obj U = ⊤ := (@local_ring.closed_point_mem_iff R _ _ _).mp hU,
  rw this,
  apply_instance,
end

@[reassoc]
lemma germ_stalk_closed_point_to (R : CommRing) [local_ring R]
  (f : Scheme.Spec.obj (op R) ⟶ X)
  (U : opens X.carrier) (hU : f.1.base (closed_point R : _) ∈ U) :
  X.presheaf.germ ⟨_, hU⟩ ≫ stalk_closed_point_to R f = f.1.c.app (op U)
    ≫ @@inv _ _ (structure_sheaf.is_iso_to_open_of_closed_point_mem R f U hU) :=
begin
  haveI H := structure_sheaf.is_iso_to_open_of_closed_point_mem R f U hU,
  rw stalk_closed_point_to,
  erw [PresheafedSpace.stalk_map_germ_assoc _ _ ⟨_, _⟩],
  slice_lhs 2 3 { erw structure_sheaf.germ_comp_stalk_to_fiber_ring_hom _ _ ⟨_, _⟩ },
  congr' 1,
  apply @@is_iso.eq_inv_of_hom_inv_id _ H,
  erw [← category.assoc, iso.comp_inv_eq_id],
  ext,
  refl,
end

@[reassoc]
lemma germ_stalk_closed_point_to_to_open (R : CommRing) [local_ring R]
  (f : Scheme.Spec.obj (op R) ⟶ X)
  (U : opens X.carrier) (hU : f.1.base (local_ring.closed_point R : _) ∈ U) :
  X.presheaf.germ ⟨_, hU⟩ ≫ stalk_closed_point_to R f
    ≫ structure_sheaf.to_open R ((opens.map f.val.base).obj U) = f.1.c.app (op U) :=
begin
  haveI H := structure_sheaf.is_iso_to_open_of_closed_point_mem R f U hU,
  rw germ_stalk_closed_point_to_assoc,
  erw @@is_iso.inv_hom_id _ _ H,
  exact category.comp_id _
end

instance {X Y : Scheme} (f : X ⟶ Y)
  [H : is_open_immersion f] (U) : is_iso (f.inv_app U) :=
by { delta Scheme.hom.inv_app, apply_instance }

@[reassoc]
lemma Spec_map_stalk_closed_point_to_from_stalk (R : CommRing) [local_ring R]
  (f : Scheme.Spec.obj (op R) ⟶ X) :
  Scheme.Spec.map (stalk_closed_point_to R f).op ≫ X.from_Spec_stalk _ = f :=
begin
  rw [Scheme.from_Spec_stalk, is_affine_open.from_Spec_stalk, ← functor.map_comp_assoc,
    ← op_comp],
  convert is_open_immersion.lift_fac _ _ _,
  rotate, { apply_instance },
  { rw [is_affine_open.from_Spec_range, ← set.image_univ,
      set.image_subset_iff, ← opens.map_coe],
    convert (@opens.coe_top (prime_spectrum R) _).symm.subset using 2,
    rw ← @local_ring.closed_point_mem_iff R,
    exact X.affine_cover.covers _ },
  { refine eq.trans _ (Scheme.Spec.image_preimage _),
    rw ← quiver.hom.op_unop (Scheme.Spec.preimage _),
    congr' 2,
    rw [germ_stalk_closed_point_to],
    erw @@is_iso.comp_inv_eq _ _ (structure_sheaf.is_iso_to_open_of_closed_point_mem R f _ _),
    rw ← structure_sheaf.to_open_res _ _ _ (hom_of_le le_top),
    swap, { apply_instance },
    erw [Spec_Γ_naturality'_assoc, Scheme.Spec.image_preimage],
    let U := (X.affine_cover.map (f.1.base (closed_point R : _))).opens_range,
    have hU : is_affine_open U := range_is_affine_open_of_open_immersion _,
    have : hU.from_Spec.opens_functor.obj ⊤ = U :=
      opens.ext (set.image_univ.trans hU.from_Spec_range),
    convert_to f.1.c.app (op U) = to_Spec_Γ (X.presheaf.obj $ op U) ≫ _,
    rw [Scheme.Γ_map, quiver.hom.unop_op, is_open_immersion.lift_app, category.assoc,
      category.assoc, ← category.assoc,
      (is_iso.eq_inv_comp _).mpr (f.1.c.naturality (eq_to_hom this.symm).op)],
    erw ← functor.map_comp,
    congr' 2,
    rw [Scheme.hom.inv_app, ← is_iso.comp_inv_eq, ← functor.map_inv, ← op_inv, inv_eq_to_hom,
      PresheafedSpace.is_open_immersion.inv_inv_app,
      nat_trans.naturality_assoc, is_affine_open.from_Spec_app_eq],
    simp only [eq_to_hom_op, eq_to_hom_map, eq_to_hom_trans, category.assoc,
      eq_to_hom_refl, category.comp_id],
    refl }
end

-- lemma Spec_map_comp_from_Spec_app {R : Type*} [comm_ring R] {X : Scheme} {U : opens X.carrier}
--   (hU : is_affine_open U) (f : X.presheaf.obj (op U) ⟶ CommRing.of R) :
--   (Scheme.Spec.map f.op ≫ hU.from_Spec).1.c.app (op U) = f ≫
--     structure_sheaf.to_open R ((opens.map (Scheme.Spec.map f.op ≫ hU.from_Spec).1.base).obj U) :=
-- begin
--   rw [Scheme.comp_val_c_app, is_affine_open.from_Spec_app_eq, category.assoc,
--     nat_trans.naturality, ← category.assoc],
--   convert_to (Γ_Spec.adjunction.counit.app (op (CommRing.of R)) ≫ f.op).unop ≫ _ = _,
--   { congr' 1, rw ← Γ_Spec.adjunction.counit_naturality f.op, refl },
--   convert_to (f ≫ to_Spec_Γ (CommRing.of R)) ≫ _ = _,
--   rw category.assoc,
--   congr' 1
-- end

lemma Spec_to_equiv_of_local_ring_eq_iff {R : CommRing} [local_ring R] {X : Scheme}
  {f₁ f₂ : Σ (x : X.carrier), { f : X.presheaf.stalk x ⟶ R // is_local_ring_hom f }} :
  f₁ = f₂ ↔ ∃ h₁ : f₁.1 = f₂.1, f₁.2.1 =
    X.presheaf.stalk_specializes (specializes_of_eq h₁.symm) ≫ f₂.2.1 :=
begin
  split,
  { rintro rfl, refine ⟨rfl, by simp⟩ },
  { rcases ⟨f₁, f₂⟩ with ⟨⟨_, ⟨⟩⟩, _, ⟨⟩⟩, dsimp, rintro ⟨rfl, rfl⟩, congr' 2,
    apply Top.presheaf.stalk_hom_ext, intros U hU, simp },
end

@[reassoc]
lemma Scheme.stalk_specializes_from_Spec_stalk {X : Scheme} {x y : X.carrier} (h : x ⤳ y) :
  Scheme.Spec.map (X.presheaf.stalk_specializes h).op ≫ X.from_Spec_stalk y =
    X.from_Spec_stalk x :=
begin
  rw Scheme.from_Spec_stalk,
  generalize_proofs _ _ h₁ h₂,
  rw ← h₁.from_Spec_stalk_eq _ (h.mem_open (X.affine_cover.map y).opens_range.2 h₂),
  delta is_affine_open.from_Spec_stalk,
  rw [← Scheme.Spec.map_comp_assoc, ← op_comp, Top.presheaf.germ_stalk_specializes'],
  refl
end

def Spec_to_equiv_of_local_ring (R : CommRing) [local_ring R] (X : Scheme) :
  (Scheme.Spec.obj (op R) ⟶ X) ≃
    Σ (x : X.carrier), { f : X.presheaf.stalk x ⟶ R // is_local_ring_hom f } :=
{ to_fun := λ f, ⟨f.1.base (closed_point R : _), stalk_closed_point_to R f, infer_instance⟩,
  inv_fun := λ xf, Scheme.Spec.map xf.2.1.op ≫ X.from_Spec_stalk xf.1,
  left_inv := Spec_map_stalk_closed_point_to_from_stalk R,
  right_inv := begin
    rintros ⟨x, f, hf⟩,
    resetI,
    have : (Scheme.Spec.map f.op ≫ X.from_Spec_stalk x).1.base (closed_point R : _) = x,
    { convert_to (X.from_Spec_stalk x).val.base (prime_spectrum.comap f $ closed_point R) = x,
      rw [local_ring.comap_closed_point, Scheme.from_Spec_stalk_closed_point] },
    refine Spec_to_equiv_of_local_ring_eq_iff.mpr ⟨_, _⟩,
    { dsimp only, exact this },
    { dsimp only,
      apply quiver.hom.op_inj,
      apply Scheme.Spec.map_injective,
      rw [← cancel_mono (X.from_Spec_stalk _), Spec_map_stalk_closed_point_to_from_stalk, op_comp,
        functor.map_comp_assoc, Scheme.stalk_specializes_from_Spec_stalk],
      apply_instance }
  end }
.

lemma stalk_closed_point_to_from_Spec_stalk {X : Scheme} (x : X.carrier) :
  stalk_closed_point_to (X.presheaf.stalk x) (X.from_Spec_stalk x) =
  X.presheaf.stalk_specializes (specializes_of_eq (Scheme.from_Spec_stalk_closed_point x).symm) :=
begin
  obtain ⟨e₁, e₂⟩ := Spec_to_equiv_of_local_ring_eq_iff.mp
    ((Spec_to_equiv_of_local_ring _ X).apply_symm_apply ⟨x, 𝟙 _, infer_instance⟩),
  dsimp [Spec_to_equiv_of_local_ring, - Scheme.Spec_map_2] at e₂,
  rw category.comp_id at e₂,
  convert e₂ using 2,
  rw Scheme.Spec.map_id,
  exact (category.id_comp _).symm,
end

lemma is_affine_open.from_Spec_stalk_app (X : Scheme)
  {x : X.carrier} {U : opens X.carrier} (h : x ∈ U) :
  (X.from_Spec_stalk x).1.c.app (op U) = X.presheaf.germ ⟨x, h⟩ ≫
    structure_sheaf.to_open (X.presheaf.stalk x)
      ((opens.map (X.from_Spec_stalk x).1.base).obj U) :=
begin
  have : (X.from_Spec_stalk x).1.base (local_ring.closed_point $ X.presheaf.stalk x : _) ∈ U,
  { rwa Scheme.from_Spec_stalk_closed_point },
  haveI H := structure_sheaf.is_iso_to_open_of_closed_point_mem
    (X.presheaf.stalk x) (X.from_Spec_stalk x) U this,
  have : X.presheaf.germ ⟨_, this⟩ ≫
    stalk_closed_point_to (X.presheaf.stalk x) (X.from_Spec_stalk x) =
     X.presheaf.germ ⟨x, h⟩,
  { rw [stalk_closed_point_to_from_Spec_stalk, Top.presheaf.germ_stalk_specializes'], refl },
  rw [germ_stalk_closed_point_to] at this,
  exact (@@is_iso.comp_inv_eq _ _ H).mp this,
end

lemma stalk_map_from_Spec_stalk
  {X Y : Scheme} (f : X ⟶ Y) (x : X.carrier) :
    Scheme.Spec.map (PresheafedSpace.stalk_map f.1 x).op ≫ Y.from_Spec_stalk _ =
      X.from_Spec_stalk x ≫ f :=
begin
  apply (@equiv.apply_eq_iff_eq_symm_apply _ _ (Spec_to_equiv_of_local_ring _ Y).symm
    ⟨f.1.base x, PresheafedSpace.stalk_map f.1 x, infer_instance⟩ _).mpr _,
  refine Spec_to_equiv_of_local_ring_eq_iff.mpr ⟨_, _⟩,
  { dsimp [Spec_to_equiv_of_local_ring], rw Scheme.from_Spec_stalk_closed_point },
  { apply Scheme.stalk_hom_affine_ext,
    intros U hU hxU,
    dsimp [Spec_to_equiv_of_local_ring],
    rw Top.presheaf.germ_stalk_specializes'_assoc,
    erw PresheafedSpace.stalk_map_germ f.1 U ⟨x, hxU⟩,
    convert (germ_stalk_closed_point_to _ (X.from_Spec_stalk x ≫ f) _ _).symm using 1,
    erw @@is_iso.eq_comp_inv _ _ (structure_sheaf.is_iso_to_open_of_closed_point_mem _ _ _ _),
    rw Scheme.comp_val_c_app,
    dsimp only [functor.op],
    rw is_affine_open.from_Spec_stalk_app, swap, { exact hxU },
    exact category.assoc _ _ _ }
end

end local_ring_to_Scheme

section residue_field

variables {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)

def Scheme.residue_field (X : Scheme) (x : X.carrier) : CommRing :=
CommRing.of $ local_ring.residue_field (X.presheaf.stalk x)

instance {x : X.carrier} : field (X.residue_field x) :=
show field (local_ring.residue_field _), by apply_instance

def Scheme.to_residue_field (X : Scheme) (x) : X.stalk x ⟶ X.residue_field x :=
local_ring.residue _ 

def Scheme.desc_residue_field {K : Type*} [field K] (X : Scheme) {x}
  (f : X.stalk x ⟶ CommRing.of K) [is_local_ring_hom f] : X.residue_field x ⟶ CommRing.of K :=
local_ring.lift_residue_field f

@[simp, reassoc]
lemma Scheme.to_desc_residue_field {K : Type*} [field K] (X : Scheme) {x}
  (f : X.stalk x ⟶ CommRing.of K) [is_local_ring_hom f] :
  X.to_residue_field x ≫ X.desc_residue_field f = f := 
ring_hom.ext (λ _, rfl)

instance (x) : epi (X.to_residue_field x) :=
begin
  refine (forget _).epi_of_epi_map _,
  exact (epi_iff_surjective _).mpr ideal.quotient.mk_surjective
end

instance (x) : is_local_ring_hom (X.to_residue_field x) := local_ring.is_local_ring_hom_residue

def Scheme.residue_field_of_eq (X : Scheme) {x y : X.carrier} (h : x = y) :
  X.residue_field y ⟶ X.residue_field x :=
X.desc_residue_field
  (X.presheaf.stalk_specializes (specializes_of_eq h) ≫ X.to_residue_field x)

@[simp, reassoc]
lemma Scheme.to_residue_field_of_eq (x y) (e : x = y) :
  X.to_residue_field _ ≫ X.residue_field_of_eq e =
    (X.presheaf.stalk_congr $ inseparable.of_eq e.symm).hom ≫ X.to_residue_field _ :=
rfl

@[simp, reassoc]
lemma Scheme.residue_field_of_eq_trans (X : Scheme) {x y z : X.carrier} (h : x = y) (h' : y = z) :
  X.residue_field_of_eq h' ≫ X.residue_field_of_eq h = X.residue_field_of_eq (h.trans h') :=
by { rw ← cancel_epi (X.to_residue_field z), simpa }

@[simp]
lemma Scheme.residue_field_of_eq_refl (X : Scheme) {x : X.carrier} :
  X.residue_field_of_eq (refl x) = 𝟙 _ :=
begin
  rw [← cancel_epi (X.to_residue_field x), Scheme.to_residue_field_of_eq,
    Top.presheaf.stalk_congr_hom],
  erw [X.presheaf.stalk_specializes_refl x, category.id_comp],
end

def Scheme.hom.map_residue_field {X Y : Scheme} (f : X ⟶ Y) (x : X.carrier) :
  Y.residue_field (f.1.base x) ⟶ X.residue_field x :=
Y.desc_residue_field (PresheafedSpace.stalk_map f.1 x ≫ X.to_residue_field x)

@[simp, reassoc]
lemma Scheme.to_residue_field_map_residue_field {X Y : Scheme} (f : X ⟶ Y) (x : X.carrier) :
  Y.to_residue_field (f.1.base x) ≫ f.map_residue_field x =
    PresheafedSpace.stalk_map f.1 x ≫ X.to_residue_field x :=
Y.to_desc_residue_field (PresheafedSpace.stalk_map f.1 x ≫ X.to_residue_field x)

def Scheme.from_Spec_residue_field (X : Scheme) (x : X.carrier) :
  Scheme.Spec.obj (op $ X.residue_field x) ⟶ X :=
Scheme.Spec.map (CommRing.of_hom $ local_ring.residue _).op ≫ X.from_Spec_stalk x

@[instance]
lemma Scheme.mono_from_Spec_residue_field {X : Scheme} (x : X.carrier) :
  mono (X.from_Spec_residue_field x) :=
begin
  rw Scheme.from_Spec_residue_field,
  apply_with mono_comp { instances := ff },
  swap, { apply_instance },
  apply_with functor.map_mono { instances := ff },
  { apply_instance },
  apply_with category_theory.op_mono_of_epi { instances := ff },
  apply concrete_category.epi_of_surjective,
  exact ideal.quotient.mk_surjective,
end

@[simp, reassoc]
lemma Scheme.residue_field_of_eq_from_Spec (X : Scheme) {x y : X.carrier} (h : x = y) :
  Scheme.Spec.map (X.residue_field_of_eq h).op ≫ X.from_Spec_residue_field y =
    X.from_Spec_residue_field x :=
begin
  subst h,
  rw [Scheme.residue_field_of_eq_refl, op_id, category_theory.functor.map_id, category.id_comp],
end

lemma Scheme.hom.map_residue_field_from_Spec_residue_field
  {X Y : Scheme} (f : X ⟶ Y) (x : X.carrier) :
    Scheme.Spec.map (f.map_residue_field x).op ≫ Y.from_Spec_residue_field _ =
      X.from_Spec_residue_field x ≫ f :=
begin
  rw [Scheme.from_Spec_residue_field, Scheme.from_Spec_residue_field, category.assoc,
    ← stalk_map_from_Spec_stalk, ← functor.map_comp_assoc, ← op_comp],
  convert eq.trans _ (Scheme.Spec.map_comp_assoc _ _ _),
  all_goals { delta PresheafedSpace.stalk, cases X.presheaf.stalk x, refl },
end

lemma Scheme.hom.map_residue_field_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  (x : X.carrier) :
  (f ≫ g).map_residue_field x = g.map_residue_field (f.1.base x) ≫ f.map_residue_field x :=
begin
  apply ideal.quotient.ring_hom_ext,
  transitivity (local_ring.residue (X.presheaf.stalk x)).comp
    (PresheafedSpace.stalk_map (f ≫ g).1 x),
  { refl },
  { erw PresheafedSpace.stalk_map.comp, ext, refl }
end
.
lemma Scheme.hom.map_residue_field_congr {X Y : Scheme} {f g : X ⟶ Y} (e : f = g)
  (x : X.carrier) :
  f.map_residue_field x = Y.residue_field_of_eq (by rw e) ≫ g.map_residue_field x :=
begin
  subst e,
  rw [Scheme.residue_field_of_eq_refl, category.id_comp],
end

lemma Scheme.hom.map_residue_field_eq {X Y : Scheme} (f : X ⟶ Y) (x) : 
  f.map_residue_field x = local_ring.residue_field.map (PresheafedSpace.stalk_map f.1 x) :=
begin
  ext, refl,
end

instance {X Y : Scheme} (f : X ⟶ Y) [is_open_immersion f] (x) : 
  is_iso (f.map_residue_field x) :=
begin
  rw [CommRing.is_iso_iff_bijective, Scheme.hom.map_residue_field_eq],
  exact (local_ring.residue_field.map_equiv
    (as_iso $ PresheafedSpace.stalk_map f.1 x).CommRing_iso_to_ring_equiv).bijective
end

lemma Scheme.from_Spec_residue_field_base (x : X.carrier) (s) :
  (X.from_Spec_residue_field x).1.base s = x :=
begin
  rw [Scheme.from_Spec_residue_field, Scheme.comp_val_base, comp_apply],
  convert Scheme.from_Spec_stalk_closed_point x,
  convert prime_spectrum.comap_residue _,
end

lemma Scheme.range_from_Spec_residue_field  (x : X.carrier) :
  set.range (X.from_Spec_residue_field x).1.base = {x} :=
begin
  ext y,
  simp only [set.mem_range, set.mem_singleton_iff, Scheme.from_Spec_residue_field_base],
  exact ⟨λ ⟨a, b⟩, b.symm, λ e, ⟨(⊥ : prime_spectrum (X.residue_field x)), e.symm⟩⟩,
end
.
lemma Spec_map_desc_residue_field_from_Spec_residue_field (K : Type*) [field K] (X : Scheme)
  (f : Scheme.Spec.obj (op $ CommRing.of K) ⟶ X) :
  Scheme.Spec.map (X.desc_residue_field (stalk_closed_point_to _ f)).op
    ≫ X.from_Spec_residue_field (f.1.base (local_ring.closed_point K)) = f :=
begin
  dsimp only [Scheme.from_Spec_residue_field],
  rw [← Scheme.Spec.map_comp_assoc, ← op_comp],
  exact Spec_map_stalk_closed_point_to_from_stalk _ f
end

lemma Spec_to_equiv_of_field_eq_iff {K : Type*} [field K] {X : Scheme}
  {f₁ f₂ : Σ x : X.carrier, X.residue_field x ⟶ CommRing.of K} :
  f₁ = f₂ ↔ ∃ e : f₁.1 = f₂.1,f₁.2 = X.residue_field_of_eq e.symm ≫ f₂.2 :=
by { split, { rintro rfl, exact ⟨rfl, by simp⟩ },
  { cases f₁, cases f₂, dsimp, rintro ⟨rfl, rfl⟩, congr, simp  } }

lemma Spec_to_equiv_of_field_right_inv {K : Type*} [field K] {X : Scheme}
  (xf : Σ x : X.carrier, X.residue_field x ⟶ CommRing.of K) :
  (sigma.mk _ (X.desc_residue_field (stalk_closed_point_to _ $
    Scheme.Spec.map xf.2.op ≫ X.from_Spec_residue_field xf.1)) :
      Σ x : X.carrier, X.residue_field x ⟶ CommRing.of K) = xf :=
begin
  haveI : nontrivial (CommRing.of K) := show nontrivial K, by apply_instance,
  refine Spec_to_equiv_of_field_eq_iff.mpr ⟨_, _⟩,
  { exact Scheme.from_Spec_residue_field_base _ _ },
  apply ideal.quotient.ring_hom_ext,
  dsimp,
  convert_to stalk_closed_point_to (CommRing.of K)
    (Scheme.Spec_map xf.snd ≫ X.from_Spec_residue_field xf.fst) = _,
  have := is_local_ring_hom_comp xf.2 (local_ring.residue $ X.presheaf.stalk xf.1),
  obtain ⟨_, e₂⟩ := Spec_to_equiv_of_local_ring_eq_iff.mp ((Spec_to_equiv_of_local_ring _ X)
    .right_inv ⟨xf.1, CommRing.of_hom (local_ring.residue _) ≫ xf.2, this⟩),
  dsimp only [Spec_to_equiv_of_local_ring] at e₂,
  convert e₂ using 1,
  congr' 1,
  rw [op_comp, Scheme.Spec.map_comp_assoc],
  refl
end
.

@[simps]
def Spec_to_equiv_of_field (K : Type*) [field K] (X : Scheme) :
  (Scheme.Spec.obj (op $ CommRing.of $ K) ⟶ X) ≃
    Σ x : X.carrier, X.residue_field x ⟶ CommRing.of K :=
{ to_fun := λ f, ⟨_, X.desc_residue_field (stalk_closed_point_to _ f)⟩,
  inv_fun := λ xf, Scheme.Spec.map xf.2.op ≫ X.from_Spec_residue_field xf.1,
  left_inv := Spec_map_desc_residue_field_from_Spec_residue_field K X,
  right_inv := Spec_to_equiv_of_field_right_inv }

end residue_field

end algebraic_geometry
