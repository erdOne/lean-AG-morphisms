import algebraic_geometry.AffineScheme
import for_mathlib.localized_module

open category_theory category_theory.limits opposite topological_space

namespace algebraic_geometry

universes v u

lemma structure_sheaf.open_to_localization_localization_to_stalk {R : Type*} [comm_ring R]
  (U : opens (prime_spectrum.Top R)) (x : U) :
  structure_sheaf.open_to_localization R U x x.2 ≫ structure_sheaf.localization_to_stalk R x =
    (Spec.structure_sheaf R).presheaf.germ x :=
begin
  rw [← structure_sheaf.germ_comp_stalk_to_fiber_ring_hom, category.assoc,
    structure_sheaf.stalk_to_fiber_ring_hom_localization_to_stalk, category.comp_id],
end

lemma specializes_of_eq {α : Type*} [topological_space α] {x y : α} (e : x = y) :
  x ⤳ y := e ▸ specializes_refl x

@[simp, reassoc, elementwise]
lemma _root_.Top.presheaf.stalk_specializes_comp {C : Type*} [category C] [limits.has_colimits C]
  {X : Top} (F : X.presheaf C)
  {x y z : X} (h : x ⤳ y) (h' : y ⤳ z) :
  F.stalk_specializes h' ≫ F.stalk_specializes h = F.stalk_specializes (h.trans h') :=
F.stalk_hom_ext $ λ _ _, by simp

@[simp]
lemma _root_.Top.presheaf.stalk_specializes_refl {C : Type*} [category C] [limits.has_colimits C]
  {X : Top} (F : X.presheaf C) (x : X) :
  F.stalk_specializes (specializes_refl x) = 𝟙 _ :=
F.stalk_hom_ext $ λ _ _, by { dsimp, simpa }

lemma _root_.Top.presheaf.stalk_hom_ext_of_is_basis {C : Type*} [category C] [limits.has_colimits C] {X : Top}
  {B : set (opens X)} (hB : opens.is_basis B)
  (F : X.presheaf C) {x} {Y : C}
  {f₁ f₂ : F.stalk x ⟶ Y}
  (ih : ∀ (U ∈ B) (hxU : x ∈ U), F.germ ⟨x, hxU⟩ ≫ f₁ = F.germ ⟨x, hxU⟩ ≫ f₂) : f₁ = f₂ :=
Top.presheaf.stalk_hom_ext _
begin
  intros U hxU,
  obtain ⟨V, hV, hxV, hVU : V ≤ U⟩ := opens.is_basis_iff_nbhd.mp hB hxU,
  have := congr_arg (λ f, F.map (hom_of_le hVU).op ≫ f) (ih V hV hxV),
  convert this using 1; rw [← category.assoc, F.germ_res]; refl
end

lemma Scheme.stalk_hom_affine_ext {X : Scheme} (x : X.carrier) {Y : CommRing}
  {f₁ f₂ : X.stalk x ⟶ Y} (ih : ∀ (U : opens X.carrier) (hU : is_affine_open U) (hxU : x ∈ U),
    X.presheaf.germ ⟨x, hxU⟩ ≫ f₁ = X.presheaf.germ ⟨x, hxU⟩ ≫ f₂) : f₁ = f₂ :=
Top.presheaf.stalk_hom_ext_of_is_basis (is_basis_affine_open X) _ ih

@[reassoc]
lemma Spec_Γ_naturality' {R S : CommRing} (f : R ⟶ S) :
  f ≫ to_Spec_Γ S = to_Spec_Γ R ≫ Scheme.Γ.map (Scheme.Spec.map f.op).op :=
Spec_Γ_naturality f

@[simp, reassoc]
lemma PresheafedSpace.stalk_map_germ' {C : Type u} [category.{v} C] [has_colimits C]
  {X Y : PresheafedSpace.{v} C} (α : X ⟶ Y) (x : X) {U : opens Y} (hxU : α.base x ∈ U) :
  Y.presheaf.germ ⟨α.base x, hxU⟩ ≫ PresheafedSpace.stalk_map α x = α.c.app _ ≫
    X.presheaf.germ ⟨x, show x ∈ (opens.map α.base).obj U, from hxU⟩ :=
PresheafedSpace.stalk_map_germ α U ⟨_, _⟩

lemma PresheafedSpace.stalk_map.congr_hom' {C : Type u} [category.{v} C] [has_colimits C]
  {X Y : PresheafedSpace.{v} C} (α β : X ⟶ Y) (h : α = β) (x : X) :
  PresheafedSpace.stalk_map α x =
    Y.presheaf.stalk_specializes (by subst h) ≫ PresheafedSpace.stalk_map β x :=
begin
  subst h,
  apply Top.presheaf.stalk_hom_ext, 
  intros U hxU,
  simp,
end

instance {R : Type*} [comm_ring R] [local_ring R] : 
  is_iso (structure_sheaf.to_stalk R (local_ring.closed_point R)) :=
begin
  have : ∀ x : (local_ring.closed_point R).as_ideal.prime_compl, is_unit (x : R),
  { exact λ x, not_not.mp x.2 },
  have : is_iso (is_localization.at_units R
    (local_ring.closed_point R).as_ideal.prime_compl
    ((Spec.structure_sheaf R).presheaf.stalk
    (local_ring.closed_point R)) this).to_ring_equiv.to_CommRing_iso.hom := infer_instance,
  convert this using 1,
  let S := _, change S = CommRing.of S, clear_value S, cases S, refl 
end

instance {C} [category C] [has_colimits C] {X : Top} (F : X.presheaf C) {x y} (e : x = y) :
  is_iso (F.stalk_specializes (specializes_of_eq e)) :=
⟨⟨F.stalk_specializes (specializes_of_eq e.symm), by simp, by simp⟩⟩

lemma Γ_Spec.adjunction_unit_app_base_apply  {X : Scheme} (x) :
  (Γ_Spec.adjunction.unit.app X).1.base x =
    prime_spectrum.comap (X.to_LocallyRingedSpace.Γ_to_stalk x) (local_ring.closed_point _) :=
rfl

lemma morphism_restrict_val_base {X Y : Scheme} (f : X ⟶ Y) (U : opens Y.carrier) :
  ⇑(f ∣_ U).1.base = U.1.restrict_preimage f.1.base :=
funext (λ x, subtype.ext (morphism_restrict_base_coe f U x))

/-- The stalks are isomorphic on inseparable points -/
@[simps] noncomputable
def _root_.Top.presheaf.stalk_congr {X : Top} {C : Type*} [category C] [has_colimits C]
  (F : X.presheaf C) {x y : X}
  (e : inseparable x y) : F.stalk x ≅ F.stalk y :=
⟨F.stalk_specializes e.ge, F.stalk_specializes e.le, by simp, by simp⟩

lemma _root_.inseparable.of_eq {α :Type*} [topological_space α] {x y :α} 
  (e : x = y) : inseparable x y := e ▸ inseparable.refl x

/--
The stalk map of a restriction of a morphism is isomorphic to the stalk map of the original map.
-/
noncomputable
def morphism_restrict_stalk_map {X Y : Scheme} (f : X ⟶ Y) (U : opens Y.carrier) (x) :
  arrow.mk (PresheafedSpace.stalk_map (f ∣_ U).1 x) ≅
    arrow.mk (PresheafedSpace.stalk_map f.1 x.1) :=
begin
  fapply arrow.iso_mk',
  { refine Y.restrict_stalk_iso U.open_embedding ((f ∣_ U).1 x) ≪≫ Top.presheaf.stalk_congr _ _,
    apply inseparable.of_eq,
    exact morphism_restrict_base_coe f U x },
  { exact X.restrict_stalk_iso _ _ },
  { apply Top.presheaf.stalk_hom_ext,
    intros V hxV,
    simp only [Top.presheaf.stalk_congr_hom, category_theory.category.assoc,
      category_theory.iso.trans_hom],
    erw PresheafedSpace.restrict_stalk_iso_hom_eq_germ_assoc,
    erw PresheafedSpace.stalk_map_germ_assoc _ _ ⟨_, _⟩,
    rw [Top.presheaf.germ_stalk_specializes'_assoc],
    erw PresheafedSpace.stalk_map_germ _ _ ⟨_, _⟩,
    erw PresheafedSpace.restrict_stalk_iso_hom_eq_germ,
    rw [morphism_restrict_c_app, category.assoc, Top.presheaf.germ_res],
    refl }
end


namespace structure_sheaf

noncomputable theory

open Spec

variables {R S : CommRing.{u}} (f : R ⟶ S) (p : prime_spectrum R)

/--
For an algebra `f : R →+* S`, this is the ring homomorphism `S →+* (f∗ 𝒪ₛ)ₚ` for a `p : Spec R`.
This is shown to be the localization at `p` in `is_localized_module_to_pushforward_stalk_alg_hom`.
-/
def to_pushforward_stalk :
  S ⟶ (Spec.Top_map f _* (structure_sheaf S).1).stalk p :=
structure_sheaf.to_open S ⊤ ≫
  @Top.presheaf.germ _ _ _ _ (Spec.Top_map f _* (structure_sheaf S).1) ⊤ ⟨p, trivial⟩

@[reassoc]
lemma to_pushforward_stalk_comp :
  f ≫ structure_sheaf.to_pushforward_stalk f p =
  structure_sheaf.to_stalk R p ≫
    (Top.presheaf.stalk_functor _ _).map (Spec.SheafedSpace_map f).c :=
begin
  rw structure_sheaf.to_stalk,
  erw category.assoc,
  rw Top.presheaf.stalk_functor_map_germ,
  exact Spec_Γ_naturality_assoc f _,
end

instance : algebra R ((Spec.Top_map f _* (structure_sheaf S).1).stalk p) :=
(f ≫ structure_sheaf.to_pushforward_stalk f p).to_algebra

lemma algebra_map_pushforward_stalk :
  algebra_map R ((Spec.Top_map f _* (structure_sheaf S).1).stalk p) =
    f ≫ structure_sheaf.to_pushforward_stalk f p := rfl

variables (R S) [algebra R S]

/--
This is the `alg_hom` version of `to_pushforward_stalk`, which is the map `S ⟶ (f∗ 𝒪ₛ)ₚ` for some
algebra `R ⟶ S` and some `p : Spec R`.
-/
@[simps]
def to_pushforward_stalk_alg_hom :
  S →ₐ[R] (Spec.Top_map (algebra_map R S) _* (structure_sheaf S).1).stalk p :=
{ commutes' := λ _, rfl, ..(structure_sheaf.to_pushforward_stalk (algebra_map R S) p) }

.
lemma is_localized_module_to_pushforward_stalk_alg_hom_aux (y) :
  ∃ (x : S × p.as_ideal.prime_compl), x.2 • y = to_pushforward_stalk_alg_hom R S p x.1 :=
begin
  obtain ⟨U, hp, s, e⟩ := Top.presheaf.germ_exist _ _ y,
  obtain ⟨_, ⟨r, rfl⟩, hpr, hrU⟩ := prime_spectrum.is_topological_basis_basic_opens
    .exists_subset_of_mem_open (show p ∈ U.1, from hp) U.2,
  change prime_spectrum.basic_open r ≤ U at hrU,
  replace e := ((Spec.Top_map (algebra_map R S) _* (structure_sheaf S).1)
    .germ_res_apply (hom_of_le hrU) ⟨p, hpr⟩ _).trans e,
  set s' := (Spec.Top_map (algebra_map R S) _* (structure_sheaf S).1).map (hom_of_le hrU).op s
    with h,
  rw ← h at e,
  clear_value s', clear_dependent U,
  obtain ⟨⟨s, ⟨_, n, rfl⟩⟩, hsn⟩ := @is_localization.surj _ _ _
    _ _ _ (structure_sheaf.is_localization.to_basic_open S $ algebra_map R S r) s',
  refine ⟨⟨s, ⟨r, hpr⟩ ^ n⟩, _⟩,
  rw [submonoid.smul_def, algebra.smul_def, algebra_map_pushforward_stalk, to_pushforward_stalk,
    comp_apply, comp_apply],
  iterate 2 { erw ← (Spec.Top_map (algebra_map R S) _* (structure_sheaf S).1).germ_res_apply
    (hom_of_le le_top) ⟨p, hpr⟩ },
  rw [← e, ← map_mul, mul_comm],
  dsimp only [subtype.coe_mk] at hsn,
  rw ← map_pow (algebra_map R S) at hsn,
  congr' 1
end

instance is_localized_module_to_pushforward_stalk_alg_hom :
  is_localized_module p.as_ideal.prime_compl (to_pushforward_stalk_alg_hom R S p).to_linear_map :=
begin
  apply is_localized_module.mk_of_algebra,
  { intros x hx, rw [algebra_map_pushforward_stalk, to_pushforward_stalk_comp, comp_apply],
    exact (is_localization.map_units ((structure_sheaf R).presheaf.stalk p) ⟨x, hx⟩).map _ },
  { apply is_localized_module_to_pushforward_stalk_alg_hom_aux },
  { intros x hx,
    rw [to_pushforward_stalk_alg_hom_apply, ring_hom.to_fun_eq_coe,
      ← (to_pushforward_stalk (algebra_map R S) p).map_zero, to_pushforward_stalk, comp_apply,
      comp_apply, map_zero] at hx,
    obtain ⟨U, hpU, i₁, i₂, e⟩ := Top.presheaf.germ_eq _ _ _ _ _ _ hx,
    obtain ⟨_, ⟨r, rfl⟩, hpr, hrU⟩ := prime_spectrum.is_topological_basis_basic_opens
      .exists_subset_of_mem_open (show p ∈ U.1, from hpU) U.2,
    change prime_spectrum.basic_open r ≤ U at hrU,
    apply_fun (Spec.Top_map (algebra_map R S) _* (structure_sheaf S).1).map (hom_of_le hrU).op at e,
    simp only [Top.presheaf.pushforward_obj_map, functor.op_map, map_zero, ← comp_apply,
      to_open_res] at e,
    have : to_open S (prime_spectrum.basic_open $ algebra_map R S r) x = 0,
    { refine eq.trans _ e, refl },
    have := (@is_localization.mk'_one _ _ _
      _ _ _ (structure_sheaf.is_localization.to_basic_open S $ algebra_map R S r) x).trans this,
    obtain ⟨⟨_, n, rfl⟩, e⟩ := (is_localization.mk'_eq_zero_iff _ _).mp this,
    refine ⟨⟨r, hpr⟩ ^ n, _⟩,
    rw [submonoid.smul_def, algebra.smul_def, submonoid.coe_pow, subtype.coe_mk, mul_comm, map_pow],
    exact e },
end

end structure_sheaf


end algebraic_geometry