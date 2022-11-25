import algebraic_geometry.AffineScheme
import for_mathlib.localized_module

open category_theory category_theory.limits opposite topological_space

namespace algebraic_geometry

universes v u


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

instance pushforward_stalk_algebra : algebra ((structure_sheaf R).presheaf.stalk p) 
  ((Spec.Top_map f _* (structure_sheaf S).1).stalk p) :=
begin
  apply ring_hom.to_algebra,
  refine (@Top.presheaf.stalk_functor CommRing _ _ (Scheme.Spec.obj $ op R).carrier p).map _,
  exact (Scheme.Spec.map f.op).1.c
end

lemma algebra_map_pushforward_stalk_algebra :
  algebra_map ((structure_sheaf R).presheaf.stalk p)
    ((Spec.Top_map f _* (structure_sheaf S).1).stalk p) =
    (@Top.presheaf.stalk_functor CommRing _ _ (Scheme.Spec.obj $ op R).carrier p).map
      (Scheme.Spec.map f.op).1.c := rfl

instance : is_scalar_tower R ((structure_sheaf R).presheaf.stalk p) 
  ((Spec.Top_map f _* (structure_sheaf S).1).stalk p) :=
begin
  apply is_scalar_tower.of_algebra_map_eq',
  exact to_pushforward_stalk_comp f p,
end

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
.

instance {R A : Type*} [comm_ring R] [comm_ring A] [algebra R A] (S : submonoid R)
  [H : is_localization S A] : is_localized_module S (algebra.of_id R A).to_linear_map :=
begin
  apply is_localized_module.mk_of_algebra,
  { exact λ x hx, H.1 ⟨x, hx⟩ },
  { simp_rw [submonoid.smul_def, algebra.smul_def, mul_comm], exact H.2 },
  { intros x hx, rw ← (algebra.of_id R A).map_zero at hx,
    simpa [submonoid.smul_def, mul_comm] using H.3.mp hx }
end

lemma _root_.algebraic_geometry.Spec.localized_module_map_iso_stalk_map :
  (is_localized_module.iso p.as_ideal.prime_compl
    (to_pushforward_stalk_alg_hom R S p).to_linear_map).to_linear_map.comp
    ((localized_module.map p.as_ideal.prime_compl
      (algebra.of_id R S).to_linear_map).restrict_scalars R) =
  (is_scalar_tower.to_alg_hom _ _ _).to_linear_map.comp
  (is_localized_module.iso p.as_ideal.prime_compl
    (algebra.of_id R ((structure_sheaf R).presheaf.stalk p)).to_linear_map).to_linear_map :=
begin
  ext x,
  induction x using localized_module.induction_on,
  rw [linear_map.comp_apply, linear_map.restrict_scalars_apply, localized_module.map_mk],
  refine is_localized_module.mk'_eq_iff.mpr _,
  rw [submonoid.smul_def, linear_map.comp_apply, ← linear_map.map_smul,
    linear_equiv.coe_to_linear_map, is_localized_module.iso_mk, ← is_localized_module.mk'_smul,
    ← submonoid.smul_def, is_localized_module.mk'_cancel],
  dsimp only [alg_hom.to_linear_map_apply, algebra.of_id_apply, is_scalar_tower.to_alg_hom_apply],
  rw ← is_scalar_tower.algebra_map_apply,
  refl,
end

lemma _root_.algebraic_geometry.Spec.localized_module_map_iso_stalk_map' :
  ((localized_module.map p.as_ideal.prime_compl
      (algebra.of_id R S).to_linear_map).restrict_scalars R) =
  (is_localized_module.iso p.as_ideal.prime_compl
    (to_pushforward_stalk_alg_hom R S p).to_linear_map).symm.to_linear_map.comp
  ((is_scalar_tower.to_alg_hom _ _ _).to_linear_map.comp
  (is_localized_module.iso p.as_ideal.prime_compl
    (algebra.of_id R ((structure_sheaf R).presheaf.stalk p)).to_linear_map).to_linear_map) :=
begin
  rw ← _root_.algebraic_geometry.Spec.localized_module_map_iso_stalk_map,
  ext1,
  exact (linear_equiv.symm_apply_apply _ _).symm
end

end structure_sheaf

end algebraic_geometry