import algebraic_geometry.AffineScheme

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

lemma prime_spectrum.Union_basic_open_eq_top_iff {R : Type*} [comm_ring R] {ι : Type*}
  (f : ι → R) : (⨆ i : ι, prime_spectrum.basic_open (f i)) = ⊤ ↔ ideal.span (set.range f) = ⊤ :=
begin
  erw opens.supr_mk (λ i : ι, (prime_spectrum.basic_open (f i)).1),
  rw [← opens.ext_iff, subtype.coe_mk],
  simp_rw [subtype.val_eq_coe, prime_spectrum.basic_open_eq_zero_locus_compl],
  rw [← set.compl_Inter, opens.coe_top],
  erw compl_eq_top,
  rw [← prime_spectrum.zero_locus_Union, ← prime_spectrum.zero_locus_span],
  erw prime_spectrum.zero_locus_empty_iff_eq_top,
  simp,
end

lemma CommRing.is_iso_iff_bijective {R S : CommRing} (f : R ⟶ S) :
  is_iso f ↔ function.bijective f :=
begin
  rw ← is_iso_iff_bijective,
  change is_iso f ↔ is_iso ((forget CommRing).map f),
  refine ⟨λ H, by exactI infer_instance, λ H, by exactI is_iso_of_reflects_iso f (forget CommRing)⟩,
end

lemma bijective_of_is_localization {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]
  [algebra R S] [algebra R T] (M : submonoid R) [is_localization M S] [is_localization M T]
  (f : S →+* T) (hf : f.comp (algebra_map R S) = algebra_map R T) : function.bijective f :=
begin
  have : f = is_localization.alg_equiv M S T,
  { apply is_localization.ring_hom_ext M, { rw hf, ext, simp }, { apply_instance } },
  rw this,
  exact (is_localization.alg_equiv M S T).to_equiv.bijective,
end

lemma Γ_Spec.adjunction.unit_app_map_basic_open {X : Scheme} (r : X.presheaf.obj (op ⊤)) :
  (opens.map (Γ_Spec.adjunction.unit.app X).1.base).obj (prime_spectrum.basic_open r) =
    X.basic_open r :=
begin
  rw ← basic_open_eq_of_affine,
  erw Scheme.preimage_basic_open,
  change X.basic_open _ = _,
  congr,
  rw [Γ_Spec.adjunction_unit_app_app_top, ← comp_apply],
  simp [-comp_apply]
end

lemma preimage_adjunction_unit_basic_open (X : Scheme) (r : X.presheaf.obj (op ⊤)) :
  (opens.map (Γ_Spec.adjunction.unit.app X).1.base).obj (prime_spectrum.basic_open r) =
    X.basic_open r :=
begin
  rw ← basic_open_eq_of_affine,
  erw Scheme.preimage_basic_open,
  congr',
  rw [Γ_Spec.adjunction_unit_app_app_top, ← comp_apply],
  simp [-comp_apply]
end

lemma supr_basic_open_eq_top_of_span_eq_top (X : Scheme) (s : set (X.presheaf.obj $ op ⊤))
  (h : ideal.span s = ⊤) : (⨆ i : s, X.basic_open i.1) = ⊤ :=
begin
  have := prime_spectrum.Union_basic_open_eq_top_iff (coe : s → X.presheaf.obj (op ⊤)),
  rw subtype.range_coe at this,
  rw ← this at h,
  apply_fun (opens.map (Γ_Spec.adjunction.unit.app X).1.base).obj at h,
  rw opens.map_supr at h,
  convert h,
  ext1 i,
  exact (preimage_adjunction_unit_basic_open X _).symm
end

noncomputable
def Spec_Γ_arrow_iso_of_is_affine {X Y : Scheme} (f : X ⟶ Y) [is_affine X] [is_affine Y] :
  arrow.mk f ≅ arrow.mk (Scheme.Spec.map (Scheme.Γ.map f.op).op) :=
arrow.iso_mk' _ _ (as_iso $ Γ_Spec.adjunction.unit.app _) (as_iso $ Γ_Spec.adjunction.unit.app _)
  (Γ_Spec.adjunction.unit_naturality f)

noncomputable
def Γ_Spec_arrow_iso {R S : CommRing} (f : R ⟶ S) :
  arrow.mk f ≅ arrow.mk (Scheme.Γ.map (Scheme.Spec.map f.op).op) :=
(arrow.iso_of_nat_iso Spec_Γ_identity (arrow.mk f)).symm

end algebraic_geometry