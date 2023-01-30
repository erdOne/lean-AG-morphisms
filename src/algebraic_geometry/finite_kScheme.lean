import morphisms.finite
import dimension_theory.finite_algebra
import algebraic_geometry.properties
import algebraic_geometry.coproduct

open category_theory opposite topological_space

namespace algebraic_geometry

open_locale topological_space

universe u

variables {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X.carrier)

lemma topological_space.opens.is_basis.Sup_eq_top {α : Type*} [topological_space α]
  {s : set (topological_space.opens α)} (hs : topological_space.opens.is_basis s) : Sup s = ⊤ :=
begin
  obtain ⟨s', hs₁, hs₂⟩ := topological_space.opens.is_basis_iff_cover.mp hs ⊤,
  rw [eq_top_iff, hs₂], exact Sup_le_Sup hs₁
end

local notation `𝖲𝗉𝖾𝖼` K := Scheme.Spec.obj (op $ CommRing.of $ K)

noncomputable
instance Scheme.stalk_algebra (x : X.carrier) :
  algebra (Scheme.Γ.obj (op X)) (X.stalk x) :=
(X.presheaf.germ ⟨x, show x ∈ (⊤ : topological_space.opens X.carrier), from trivial⟩).to_algebra

instance is_localization_stalk_of_is_affine [is_affine X] (x : X.carrier) :
  @is_localization.at_prime (Scheme.Γ.obj (op X)) _ (X.stalk x) _ _
    (X.iso_Spec.hom.val.base x).as_ideal _ :=
begin
  delta is_localization.at_prime,
  convert (top_is_affine_open X).is_localization_stalk ⟨x, trivial⟩,
  delta is_affine_open.prime_ideal_of,
  convert_to (X.of_restrict
    (topological_space.opens.open_embedding ⊤) ≫ X.iso_Spec.hom).1.base ⟨x, trivial⟩ = 
    (_ ≫ Scheme.Spec.map _).1.base _,
  congr' 3,
  dsimp only [Scheme.iso_Spec, as_iso_hom],
  rw [← adjunction.unit_naturality, functor.right_op_map,
    Scheme.Γ_map_op, Scheme.of_restrict_val_c_app],
  congr' 5,
end

noncomputable
def stalk_map_iso_Γ_map_localization_of_field
  {K : Type*} [field K] [is_affine X] (f : X ⟶ 𝖲𝗉𝖾𝖼 K) (x : X.carrier) : 
  arrow.mk (PresheafedSpace.stalk_map f.val x) ≅ 
    arrow.mk (to_Spec_Γ (CommRing.of K) ≫ Scheme.Γ.map f.op ≫
    CommRing.of_hom (algebra_map (Scheme.Γ.obj (op X))
      (@localization.at_prime
        (Scheme.Γ.obj (op X)) _ (X.iso_Spec.hom.val.base x).as_ideal _))) :=
begin
  symmetry,
  refine arrow.iso_mk' _ _ (as_iso _) _ _,
  { exact structure_sheaf.to_stalk K _ },
  { rw CommRing.is_iso_iff_bijective,
    refine (@@is_localization.at_units _ _ _ _ _ _ 
      (structure_sheaf.is_localization.to_stalk K _) _).bijective,
    rintro ⟨a, ha⟩, rw [subtype.coe_mk, is_unit_iff_ne_zero],
    rintro rfl, exact ha (f.1.base x).1.zero_mem },
  { exact { ..(@is_localization.alg_equiv (Scheme.Γ.obj (op X)) _
      (X.iso_Spec.hom.val.base x).as_ideal.prime_compl _ _
      localization.algebra localization.is_localization
      _ _ (Scheme.stalk_algebra x) _).to_ring_equiv.to_CommRing_iso } },
  { simp only [as_iso_hom, structure_sheaf.to_stalk, category.assoc],
    erw PresheafedSpace.stalk_map_germ',
    congr' 2,
    convert_to _ = (is_localization.alg_equiv _ _ _).to_alg_hom.to_ring_hom.comp (algebra_map _ _),
    rw [alg_hom.to_ring_hom_eq_coe, alg_hom.comp_algebra_map],
    refl }
end

noncomputable
def residue_field_map_iso_Γ_map_localization_of_field
  {K : Type*} [field K] [is_affine X] (f : X ⟶ 𝖲𝗉𝖾𝖼 K) (x : X.carrier) : 
  arrow.mk (f.map_residue_field x) ≅ 
    arrow.mk (to_Spec_Γ (CommRing.of K) ≫ Scheme.Γ.map f.op ≫
    CommRing.of_hom (algebra_map (Scheme.Γ.obj (op X))
      (@ideal.residue_field
        (Scheme.Γ.obj (op X)) _ (X.iso_Spec.hom.val.base x).as_ideal _))) :=
begin
  symmetry,
  refine arrow.iso_mk' _ _ (as_iso _) _ _,
  { exact structure_sheaf.to_stalk K (f.1.base x) ≫ (𝖲𝗉𝖾𝖼 K).to_residue_field _ },
  { rw CommRing.is_iso_iff_bijective,
    refine ⟨ring_hom.injective _, _⟩,
    refine ideal.quotient.mk_surjective.comp (@@is_localization.at_units _ _ _ _ _ _ 
      (structure_sheaf.is_localization.to_stalk K _) _).surjective,
    rintro ⟨a, ha⟩, rw [subtype.coe_mk, is_unit_iff_ne_zero],
    rintro rfl, exact ha (f.1.base x).1.zero_mem },
  { refine { ..(local_ring.residue_field.map_equiv _).to_CommRing_iso },
    exact (@is_localization.alg_equiv (Scheme.Γ.obj (op X)) _
      (X.iso_Spec.hom.val.base x).as_ideal.prime_compl _ _
      localization.algebra localization.is_localization
      _ _ (Scheme.stalk_algebra x) _).to_ring_equiv },
  { simp only [as_iso_hom, structure_sheaf.to_stalk, category.assoc,
      Scheme.to_residue_field_map_residue_field, ring_equiv.to_CommRing_iso_hom],
    erw PresheafedSpace.stalk_map_germ'_assoc,
    congr' 2,
    have : is_scalar_tower (Scheme.Γ.obj (op X)) (@localization.at_prime
        (Scheme.Γ.obj (op X)) _ (X.iso_Spec.hom.val.base x).as_ideal _) (@ideal.residue_field
        (Scheme.Γ.obj (op X)) _ (X.iso_Spec.hom.val.base x).as_ideal _) :=
      ideal.residue_field.is_scalar_tower _,
    rw [@@is_scalar_tower.algebra_map_eq _ _ _ _ _ _ _ _ _ this],
    ext x,
    simp only [category_theory.comp_apply, CommRing.of_hom_apply, function.comp_app,
      alg_equiv.to_ring_equiv_eq_coe, ring_hom.coe_comp, ring_equiv.to_ring_hom_eq_coe,
      ring_equiv.coe_to_ring_hom, local_ring.residue_field.map_equiv_apply,
      local_ring.residue_field.map],
    erw ideal.quotient.algebra_map_eq,
    rw ideal.quotient.lift_mk,
    simp only [ring_equiv.refl_apply, is_localization.alg_equiv_apply, ring_equiv.to_fun_eq_coe,
      function.comp_app, ring_hom.coe_comp, alg_equiv.coe_ring_equiv, ring_equiv.coe_to_ring_hom,
      is_localization.ring_equiv_of_ring_equiv_eq],
    refl }
end

lemma is_open_singleton_tfae_of_is_affine {K : Type*} [field K] [is_affine X] (f : X ⟶ 𝖲𝗉𝖾𝖼 K)
  [locally_of_finite_type f] (x : X.carrier) : 
  tfae [is_open ({x} : set X.carrier),
    is_clopen ({x} : set X.carrier),
    (PresheafedSpace.stalk_map f.1 x).finite,
    is_closed ({x} : set X.carrier) ∧ ∀ y, y ⤳ x → y = x] :=
begin
  simp only [is_clopen,
    ← (Top.homeo_of_iso $ Scheme.forget_to_Top.map_iso X.iso_Spec).is_open_image,
    ← (Top.homeo_of_iso $ Scheme.forget_to_Top.map_iso X.iso_Spec).is_closed_image,
    set.image_singleton],
  rw [arrow.iso_w' (stalk_map_iso_Γ_map_localization_of_field f x).symm,
    ring_hom.finite_respects_iso.cancel_left_is_iso,
    ring_hom.finite_respects_iso.cancel_right_is_iso],
  convert prime_spectrum.is_open_singleton_tfae_of_finite_type_of_field'
    (to_Spec_Γ (CommRing.of K) ≫ Scheme.Γ.map f.op) _ (X.iso_Spec.hom.1.base x) using 6,
  { rw eq_iff_iff, split,
    { intros H y hy,
      obtain ⟨y, rfl⟩ := (show function.surjective (X.iso_Spec.hom.val.base),
        by { rw ← Top.epi_iff_surjective, apply_instance }) y,
      rw H y, { exact le_rfl },
      rwa [← (Top.homeo_of_iso $ Scheme.forget_to_Top.map_iso X.iso_Spec).inducing.specializes_iff,
        ← prime_spectrum.le_iff_specializes] },
    { intros H y hy,
      refine (hy.antisymm _).eq,
      rw [← (Top.homeo_of_iso $ Scheme.forget_to_Top.map_iso X.iso_Spec).inducing.specializes_iff,
        ← prime_spectrum.le_iff_specializes] at hy ⊢,
      exact H hy } },
  { rwa [ring_hom.finite_type_respects_iso.cancel_left_is_iso, ← locally_of_finite_type_Spec_iff,
      arrow.iso_w' (Spec_Γ_arrow_iso_of_is_affine f),
    locally_of_finite_type_respects_iso.cancel_left_is_iso,
    locally_of_finite_type_respects_iso.cancel_right_is_iso] }
end

lemma _root_.closed_embedding.stable_under_specialization_image
  {α β : Type*} [topological_space α] [topological_space β] {f : α → β} (hf : closed_embedding f) 
  {s : set α} : stable_under_specialization (f '' s) ↔ stable_under_specialization s :=
⟨λ h, set.preimage_image_eq s hf.inj ▸ h.preimage hf.continuous,
  stable_under_specialization.image hf.is_closed_map.specializing_map⟩

lemma is_closed_singleton_tfae_of_is_affine {K : Type*} [field K] [is_affine X]
  (f : X ⟶ 𝖲𝗉𝖾𝖼 K)
  [locally_of_finite_type f] (x : X.carrier) :
  tfae [is_closed ({x} : set $ X.carrier),
    stable_under_specialization ({x} : set $ X.carrier),
    (f.map_residue_field x).finite] :=
begin
  rw [← (Top.homeo_of_iso $ Scheme.forget_to_Top.map_iso X.iso_Spec).is_closed_image,
    ← (Top.homeo_of_iso $ Scheme.forget_to_Top.map_iso X.iso_Spec).closed_embedding
      .stable_under_specialization_image, set.image_singleton,
    arrow.iso_w' (residue_field_map_iso_Γ_map_localization_of_field f x).symm,
    ring_hom.finite_respects_iso.cancel_left_is_iso,
    ring_hom.finite_respects_iso.cancel_right_is_iso],
  have := prime_spectrum.is_closed_singleton_tfae_of_finite_type_of_field'
    (to_Spec_Γ _ ≫ Scheme.Γ.map f.op) _ (X.iso_Spec.hom.1.base x),
  swap,
  { rwa [ring_hom.finite_type_respects_iso.cancel_left_is_iso, ← locally_of_finite_type_Spec_iff,
      arrow.iso_w' (Spec_Γ_arrow_iso_of_is_affine f),
    locally_of_finite_type_respects_iso.cancel_left_is_iso,
    locally_of_finite_type_respects_iso.cancel_right_is_iso] },
  exact (list.tfae_cons_cons.mp this).2
end

lemma is_closed_singleton_iff_finite_of_is_affine {K : Type*} [field K] [is_affine X]
  (f : X ⟶ 𝖲𝗉𝖾𝖼 K)
  [locally_of_finite_type f] (x : X.carrier) : 
  is_closed ({x} : set $ X.carrier) ↔ (f.map_residue_field x).finite :=
begin
  rw [← (Top.homeo_of_iso $ Scheme.forget_to_Top.map_iso X.iso_Spec).is_closed_image,
    set.image_singleton, arrow.iso_w' (residue_field_map_iso_Γ_map_localization_of_field f x).symm,
    ring_hom.finite_respects_iso.cancel_left_is_iso,
    ring_hom.finite_respects_iso.cancel_right_is_iso],
  refine (prime_spectrum.is_closed_singleton_iff_finite' (to_Spec_Γ _ ≫ Scheme.Γ.map f.op) _
    (X.iso_Spec.hom.1.base x)).trans _,
  { rwa [ring_hom.finite_type_respects_iso.cancel_left_is_iso, ← locally_of_finite_type_Spec_iff,
      arrow.iso_w' (Spec_Γ_arrow_iso_of_is_affine f),
    locally_of_finite_type_respects_iso.cancel_left_is_iso,
    locally_of_finite_type_respects_iso.cancel_right_is_iso] },
  refl
end

lemma is_closed_singleton_tfae {K : Type*} [field K] (f : X ⟶ 𝖲𝗉𝖾𝖼 K)
  [locally_of_finite_type f] (x : X.carrier) : 
  tfae [is_closed ({x} : set $ X.carrier),
    stable_under_specialization ({x} : set $ X.carrier),
    (f.map_residue_field x).finite] :=
begin
  obtain ⟨y, hy : ((X.affine_cover.map x).1.base) y = x⟩ := X.affine_cover.covers x,
  have hf := is_open_immersion.base_open (X.affine_cover.map x),
  have e : {y} = (X.affine_cover.map x).1.base ⁻¹' {x},
  { ext1, refine hf.inj.eq_iff.symm.trans _, rw hy, refl },
  have hX : is_jacobson X.carrier := 
    locally_of_finite_type.is_jacobson f (prime_spectrum.is_jacobson_of_is_jacobson _),
  have : (f.map_residue_field x).finite ↔ ((X.affine_cover.map x ≫ f).map_residue_field y).finite,
  { rw [Scheme.hom.map_residue_field_comp, ring_hom.finite_respects_iso.cancel_right_is_iso],
    conv_lhs { rw ← hy } },
  rw this,
  have H := is_closed_singleton_tfae_of_is_affine (X.affine_cover.map x ≫ f) y,
  tfae_have : 1 → 2, { exact is_closed.stable_under_specialization },
  tfae_have : 2 → 3, { rw H.out 2 1, intro h, convert h.preimage (X.affine_cover.map x).1.base.2 },
  tfae_have : 3 → 1,
  { rw H.out 2 0, intro h, apply hX.is_closed_of_is_locally_closed,
    convert h.is_locally_closed.image hf.to_inducing hf.2.is_locally_closed,
    rw [set.image_singleton, hy] },
  tfae_finish
end

lemma is_closed_singleton_iff_finite {K : Type*} [field K] (f : X ⟶ 𝖲𝗉𝖾𝖼 K)
  [locally_of_finite_type f] (x : X.carrier) : 
  is_closed ({x} : set $ X.carrier) ↔ (f.map_residue_field x).finite :=
begin
  have H₁ : ∀ (x : X.carrier) (U : topological_space.opens X.carrier) (hxU : x ∈ U), 
    coe ⁻¹' ({x} : set X.carrier) = ({(⟨x, hxU⟩ : U)} : set U),
  { intros x U hxU, ext y, exact @subtype.coe_inj _ _ y ⟨x, hxU⟩ },
  have H₂ : ∀ (x : X.carrier) (U : topological_space.opens X.carrier) (hxU : x ∉ U), 
    coe ⁻¹' ({x} : set X.carrier) = (∅ : set U),
  { intros x U hxU, ext ⟨y, hy⟩, refine (iff_false _).mpr _, rintro (rfl : y = x), exact hxU hy },
  split,
  { intro h,
    obtain ⟨y, hy : ((X.affine_cover.map x).1.base) y = x⟩ := X.affine_cover.covers x,
    have := (is_closed_singleton_iff_finite_of_is_affine (X.affine_cover.map x ≫ f) y).mp _,
    { rw [Scheme.hom.map_residue_field_comp,
        ring_hom.finite_respects_iso.cancel_right_is_iso] at this,
      convert this; rwa eq_comm },
    { convert h.preimage (X.affine_cover.map x).1.base.2, ext z,
      refine (is_open_immersion.base_open (X.affine_cover.map x)).inj.eq_iff.symm.trans _,
      rw hy, refl } },
  { intro h,
    rw is_closed_iff_coe_preimage_of_supr_eq_top
      ((Sup_eq_supr' _).symm.trans (is_basis_affine_open X).Sup_eq_top),
    rintro ⟨U, hU⟩,
    by_cases hxU : x ∈ U,
    { rw H₁ x U hxU,
      haveI : is_affine _ := hU,
      rwa [is_closed_singleton_iff_finite_of_is_affine (X.of_restrict U.open_embedding ≫ f) ⟨x, hxU⟩,
        Scheme.hom.map_residue_field_comp, ring_hom.finite_respects_iso.cancel_right_is_iso] },
    { rw H₂ x U hxU, exact is_closed_empty } }
end

lemma is_open_singleton_tfae {K : Type*} [field K] (f : X ⟶ 𝖲𝗉𝖾𝖼 K)
  [locally_of_finite_type f] (x : X.carrier) : 
  tfae [is_open ({x} : set X.carrier),
    is_clopen ({x} : set X.carrier),
    (PresheafedSpace.stalk_map f.1 x).finite,
    is_closed ({x} : set X.carrier) ∧ stable_under_generalization ({x} : set X.carrier)] :=
begin
  obtain ⟨U, hU, hxU⟩ : ∃ U ∈ X.affine_opens, x ∈ U,
  { rw [← topological_space.opens.mem_Sup, (is_basis_affine_open X).Sup_eq_top], trivial },
  haveI : is_affine _ := hU,
  have hX : is_jacobson X.carrier := 
    locally_of_finite_type.is_jacobson f (prime_spectrum.is_jacobson_of_is_jacobson _),
  have H₁ : coe ⁻¹' ({x} : set X.carrier) = ({(⟨x, hxU⟩ : U)} : set U),
  { ext y, exact @subtype.coe_inj _ _ y ⟨x, hxU⟩ },
  have H₃ : coe '' ({(⟨x, hxU⟩ : U)} : set U) = ({x} : set X.carrier) := set.image_singleton,
  tfae_have : 1 → 2,
  { intro h, exact ⟨h, hX.is_closed_of_is_locally_closed h.is_locally_closed⟩ },
  tfae_have : 2 → 1,
  { exact is_clopen.is_open },
  tfae_have : 1 ↔ 3,
  { rw [← H₃, ← U.prop.open_embedding_subtype_coe.open_iff_image_open,
      (is_open_singleton_tfae_of_is_affine
        (X.of_restrict U.open_embedding ≫ f) ⟨x, hxU⟩).out 0 2,
      Scheme.comp_val', PresheafedSpace.stalk_map.comp,
      ring_hom.finite_respects_iso.cancel_right_is_iso],
    refl },
  tfae_have : 2 → 4,
  { intro h, exact ⟨h.is_closed, h.is_open.stable_under_generalization⟩ },
  tfae_have : 4 → 1,
  { rintro ⟨h₁, h₂⟩,
    rw [← H₃, ← U.prop.open_embedding_subtype_coe.open_iff_image_open,
      (is_open_singleton_tfae_of_is_affine
        (X.of_restrict U.open_embedding ≫ f) ⟨x, hxU⟩).out 0 3, ← H₁],
    exact ⟨embedding_subtype_coe.to_inducing.is_closed_preimage _ h₁, λ y hy,
      subtype.ext $ h₂ (embedding_subtype_coe.to_inducing.specializes_iff.mpr hy) rfl⟩ },
  tfae_finish,
end

lemma discrete_of_finite_of_finite_type {K : Type*} [field K] (f : X ⟶ 𝖲𝗉𝖾𝖼 K)
  [locally_of_finite_type f] [_root_.finite X.carrier] : discrete_topology X.carrier :=
(locally_of_finite_type.is_jacobson f $ prime_spectrum.is_jacobson_of_is_jacobson _)
  .discrete_of_finite

lemma is_open_immersion.of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [h₁ : is_open_immersion (f ≫ g)] [h₂ : is_open_immersion g] : is_open_immersion f :=
begin
  rw is_open_immersion_iff_stalk at h₁ h₂ ⊢,
  refine ⟨open_embedding.of_comp _ h₂.1 h₁.1, λ x, _⟩,
  have := h₁.2 x,
  rw [Scheme.comp_val', PresheafedSpace.stalk_map.comp] at this,
  haveI := h₂.2 (f.1.base x),
  rw ← is_iso.inv_hom_id_assoc (PresheafedSpace.stalk_map g.1 (f.1.base x))
    (PresheafedSpace.stalk_map f.1 x),
  exactI @@is_iso.comp_is_iso _ _ this,
end

instance {X : Scheme} {U V : opens X.carrier} (e : V ⟶ U) :
  is_open_immersion (X.restrict_functor.map e).1 :=
@@is_open_immersion.of_comp _ (X.of_restrict _)
  (by { erw is_open_immersion.lift_fac, apply_instance }) _

lemma Scheme.range_restrict_functor_map (X : Scheme) {U V : opens X.carrier} (i : U ⟶ V) :
  set.range (X.restrict_functor.map i).1.val.base = (coe ⁻¹' (U : set X.carrier) : set V) :=
begin
  rw Scheme.restrict_functor_map_base,
  ext, split, { rintro ⟨x, rfl⟩, exact x.2 }, { exact λ hx, ⟨⟨x.1, hx⟩, subtype.ext rfl⟩ }
end

noncomputable
def Scheme.is_coprod_sup_of_disjoint {X : Scheme}
  {U V : opens X.carrier} (h : disjoint U V) :
  limits.is_colimit (limits.binary_cofan.mk
    (X.restrict_functor.map $ hom_of_le (le_sup_left : U ≤ U ⊔ V)).1
    (X.restrict_functor.map $ hom_of_le le_sup_right).1) :=
begin
  apply is_coprod_of_is_open_immersion_of_is_compl,
  simp only [Scheme.range_restrict_functor_map, is_compl_iff, disjoint_iff, codisjoint_iff, 
    set.sup_eq_union, set.bot_eq_empty, set.top_eq_univ, set.inf_eq_inter,
    ← opens.coe_sup, ← opens.coe_inf, ← set.preimage_inter, h.eq_bot, opens.coe_bot,
    set.preimage_empty, eq_self_iff_true, true_and, set.eq_univ_iff_forall],
  rintro ⟨x, h|h⟩,
  exacts [or.inl h, or.inr h]
end

lemma is_affine_open.of_is_closed {X : Scheme} {U V : opens X.carrier} 
  (hU : is_affine_open U) (hV : is_closed (V : set X.carrier)) (e : V ≤ U) : is_affine_open V :=
begin
  let f : X.restrict V.open_embedding ⟶ X.restrict U.open_embedding :=
    (X.restrict_functor.map e.hom).1,
  haveI : is_closed_immersion f,
  { refine is_closed_immersion_iff_is_immersion.mpr ⟨infer_instance, _⟩,
    rw Scheme.range_restrict_functor_map,
    exact hV.preimage continuous_subtype_coe },
  exact @@is_affine_of_affine f _ hU,
end

lemma is_affine_open.sup_of_disjoint {X : Scheme} {U V : opens X.carrier} 
  (hU : is_affine_open U) (hV : is_affine_open V) (h : disjoint U V) : is_affine_open (U ⊔ V) :=
begin
  haveI : is_affine _ := hU, haveI : is_affine _ := hV,
  have : X.restrict U.open_embedding ⨿ X.restrict V.open_embedding ≅ _ :=
    limits.colimit.iso_colimit_cocone ⟨_, Scheme.is_coprod_sup_of_disjoint h⟩,
  exact is_affine_of_iso this.inv
end

lemma _root_.ring_hom.finite.is_artinian_ring {R S : Type*} [comm_ring R] [comm_ring S]
  {f : R →+* S} (hf : f.finite) [is_artinian_ring R] : is_artinian_ring S :=
begin
  letI := f.to_algebra,
  exact @is_artinian_of_tower R S S _ _ _ _ _ _ _ (is_artinian_of_fg_of_artinian' hf.1)
end

lemma _root_.ring_hom.finite_type.is_noetherian_ring {R S : Type*} [comm_ring R] [comm_ring S]
  {f : R →+* S} (hf : f.finite_type) [is_noetherian_ring R] : is_noetherian_ring S :=
@@algebra.finite_type.is_noetherian_ring R S _ _ f.to_algebra hf _

lemma _root_.open_embedding.discrete_topology {α β : Type*} [topological_space α] [topological_space β]
  {f : α → β} (hf : open_embedding f) [h : discrete_topology β] : discrete_topology α :=
begin
  rw discrete_topology_iff_nhds at h ⊢,
  intro a, apply filter.map_injective hf.inj, rw [hf.map_nhds_eq, filter.map_pure, ← h],
end

lemma top_is_affine_open_iff {X : Scheme} : is_affine_open (⊤ : opens $ X.carrier) ↔ is_affine X :=
⟨λ h, @@is_affine_of_iso X.restrict_top_iso.inv _ h, @@top_is_affine_open X⟩

lemma finite_tfae_of_finite_type {K : Type*} [field K] (f : X ⟶ 𝖲𝗉𝖾𝖼 K)
  [hf : locally_of_finite_type f] [quasi_compact f] : 
  tfae [_root_.finite X.carrier,
    discrete_topology X.carrier,
    is_affine X ∧ is_artinian_ring (Scheme.Γ.obj $ op X),
    finite f] :=
begin
  have : compact_space X.carrier,
  { rw ← is_compact_univ_iff,
    exact quasi_compact.is_compact_preimage f set.univ is_open_univ is_compact_univ }, 
  tfae_have : 1 → 2,
  { introI _, exact discrete_of_finite_of_finite_type f },
  tfae_have : 2 → 1,
  { introI _, exact finite_of_compact_of_discrete },
  tfae_have : 2 → 3,
  { introI H,
    haveI := tfae_2_to_1 H,
    haveI : is_affine X,
    { rw ← forall_open_iff_discrete at H,
      have : ∀ x, is_affine_open ⟨{x}, H _⟩,
      { intro x, 
        obtain ⟨U, hU, hxU⟩ : ∃ U ∈ X.affine_opens, x ∈ U,
        { rw [← topological_space.opens.mem_Sup, (is_basis_affine_open X).Sup_eq_top], trivial },
        exact is_affine_open.of_is_closed hU ⟨H _⟩ ((@set.singleton_subset_iff _ x U).mpr hxU) },
      have : ∀ s, is_affine_open ⟨s, H _⟩,
      { intro s, apply set.finite.induction_on (set.to_finite s),
        { exact bot_is_affine_open _ },
        { intros x s hxs hs hs',
          have := is_affine_open.sup_of_disjoint hs' (this x) _,
          { convert this, simp only [subtype.coe_mk, set.union_singleton] },
          { rw disjoint_iff, ext1, simpa only [opens.coe_inf, subtype.coe_mk, opens.coe_bot,
              set.inter_singleton_eq_empty] } } },
      rw ← top_is_affine_open_iff,
      apply this },
    rw [locally_of_finite_type_respects_iso.arrow_mk_iso_iff
        (Spec_Γ_arrow_iso_of_is_affine f), locally_of_finite_type_Spec_iff,
      ← ring_hom.finite_type_respects_iso.cancel_left_is_iso (to_Spec_Γ (CommRing.of K))] at hf,
    refine ⟨‹_›, (is_artinian_ring_iff_is_noetherian_ring _).mpr ⟨hf.is_noetherian_ring,
      λ I hI, (prime_spectrum.is_closed_singleton_iff_is_maximal ⟨I, hI⟩).mp _⟩⟩,
    have := @@open_embedding.discrete_topology _ _ _
      (Top.homeo_of_iso $ Scheme.forget_to_Top.map_iso $ X.iso_Spec).symm.open_embedding H,
    rw ← forall_open_iff_discrete at this,
    exact ⟨this _⟩ },
  tfae_have : 3 → 1,
  { rintro ⟨h₁, h₂⟩,
    resetI,
    refine (Top.homeo_of_iso $ Scheme.forget_to_Top.map_iso X.iso_Spec).finite_iff.mpr _,
    exact (is_artinian_ring.is_prime_finite (Scheme.Γ.obj (op X))).to_subtype },
  tfae_have : 3 ↔ 4,
  { by_cases is_affine X, swap,
    { exact ⟨λ H, (h H.1).elim, λ H, by exactI (h $ is_affine_of_affine f).elim⟩, },
    resetI,
    rw [finite_respects_iso.arrow_mk_iso_iff (Spec_Γ_arrow_iso_of_is_affine f), finite_Spec_iff,
      ← ring_hom.finite_respects_iso.cancel_left_is_iso (to_Spec_Γ (CommRing.of K)),
      ← is_artinian_ring_iff_ring_hom_finite_of_field, and_iff_right],
    { assumption },
    { rwa [ring_hom.finite_type_respects_iso.cancel_left_is_iso, ← locally_of_finite_type_Spec_iff,
        ← locally_of_finite_type_respects_iso.arrow_mk_iso_iff
        (Spec_Γ_arrow_iso_of_is_affine f)] } },
  tfae_finish
end

lemma _root_.discrete_topology_iff_forall_is_open_singleton {α : Type*} [topological_space α] : 
  discrete_topology α ↔ ∀ x : α, is_open ({x} : set α) :=
begin
  rw ← forall_open_iff_discrete,
  refine ⟨λ h x, h _, λ h s, _⟩,
  rw ← set.bUnion_of_singleton s,
  exact is_open_bUnion (λ _ _, h _)
end

@[priority 100]
instance is_affine.compact_space [is_affine X] : compact_space X.carrier :=
by { rw ← is_compact_univ_iff, exact (top_is_affine_open X).is_compact }

lemma discrete_topology_pullback_carrier_of_finite_type {K L : Type*}
  [field K] [field L] (f : X ⟶ 𝖲𝗉𝖾𝖼 K) (g : K →+* L)
  [hf : locally_of_finite_type f] [hX : discrete_topology X.carrier] : 
  discrete_topology (limits.pullback f (Scheme.Spec.map (CommRing.of_hom g).op)).carrier :=
begin
  rw [discrete_topology_iff_forall_is_open_singleton],
  intro x,
  let 𝒰 : (limits.pullback f (Scheme.Spec.map (CommRing.of_hom g).op)).open_cover :=
    Scheme.pullback.open_cover_of_left X.affine_cover f _,
  obtain ⟨y, hy⟩ := 𝒰.covers x,
  suffices : discrete_topology (𝒰.obj $ 𝒰.f x).carrier,
  { rw [← hy, ← set.image_singleton,
      ← (is_open_immersion.base_open (𝒰.map $ 𝒰.f x)).open_iff_image_open],
    exact forall_open_iff_discrete.mpr this _ },
  haveI : quasi_compact (𝒰.map (𝒰.f x) ≫ limits.pullback.snd),
  { rw quasi_compact_over_affine_iff,
    apply_with is_affine.compact_space { instances := ff },
    apply Scheme.pullback.category_theory.limits.pullback.algebraic_geometry.is_affine },
  rw (finite_tfae_of_finite_type (𝒰.map (𝒰.f x) ≫ limits.pullback.snd)).out 1 3,
  simp only [𝒰, Scheme.pullback.open_cover_of_left_map, limits.pullback.lift_snd,
    category.comp_id],
  apply_with category_theory.limits.pullback.snd.finite { instances := ff },
  rw (finite_tfae_of_finite_type (X.affine_cover.map (𝒰.f x) ≫ f)).out 3 1,
  exact @@open_embedding.discrete_topology _ _ _
     (is_open_immersion.base_open $ X.affine_cover.map (𝒰.f x)) hX,
end

end algebraic_geometry