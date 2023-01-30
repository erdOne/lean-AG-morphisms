import morphisms.finite
import algebraic_geometry.finite_kScheme

open category_theory opposite

namespace algebraic_geometry

open_locale topological_space

universe u

variables {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X.carrier)

-- def Scheme.hom.fiber_set (y : Y.carrier) : set X.carrier := 
-- { x | f.1.base x = y }

local notation `f⁻¹f` x:100 := f.fiber (f.1.base x)

@[derive is_iso]
noncomputable
def Scheme.hom.fiber_congr {x y : Y.carrier} (e : x = y) : f.fiber x ⟶ f.fiber y :=
limits.pullback.map _ _ _ _ (𝟙 _) (Scheme.Spec.map (Y.residue_field_of_eq e).op) (𝟙 _)
  (by rw [category.comp_id, category.id_comp])
  (by rw [category.comp_id, Scheme.residue_field_of_eq_from_Spec])

@[simp, reassoc]
lemma Scheme.hom.fiber_congr_ι {x y : Y.carrier} (e : x = y) : 
  f.fiber_congr e ≫ f.fiber_ι y = f.fiber_ι x :=
(limits.pullback.lift_fst _ _ _).trans (category.comp_id _)

noncomputable
def Scheme.hom.as_fiber (x : X.carrier) : (f.fiber (f.1.base x)).carrier :=
(f.fiber_carrier (f.1.base x)).symm ⟨x, rfl⟩

lemma Scheme.hom.fiber_carrier_as_fiber (x : X.carrier) :
  ↑(f.fiber_carrier (f.1.base x) (f.as_fiber x)) = x := 
subtype.ext_iff.mp ((f.fiber_carrier (f.1.base x)).apply_symm_apply ⟨x, rfl⟩)

lemma Scheme.hom.as_fiber_fiber_carrier {y : Y.carrier} (x : (f.fiber y).carrier) :
  f.as_fiber (f.fiber_carrier y x) = (f.fiber_congr (f.fiber_carrier y x).prop.symm).1.base x := 
begin
  simp only [Scheme.hom.as_fiber, homeomorph.symm_apply_eq, Scheme.hom.fiber_carrier_apply,
    subtype.coe_mk, subtype.ext_iff, ← Scheme.comp_val_base_apply, Scheme.hom.fiber_congr_ι],
end

def Scheme.hom.quasi_finite_at (x : X.carrier) : Prop :=
𝓝[f.1.base ⁻¹' {f.1.base x} \ {x}] x = ⊥

lemma inducing.comap_nhds_within {α β : Type*} [topological_space α] [topological_space β] 
  {f : α → β} (hf : inducing f) (x : α) (s : set β) :
    filter.comap f (𝓝[s] (f x)) = 𝓝[f ⁻¹' s] x :=
by rw [nhds_within, nhds_within, filter.comap_inf, hf.nhds_eq_comap, filter.comap_principal]

lemma embedding.comap_nhds_within_ne {α β : Type*} [topological_space α] [topological_space β] 
  {f : α → β} (hf : embedding f) (x : α) : filter.comap f (𝓝[≠] (f x)) = 𝓝[≠] x :=
begin
  rw [hf.to_inducing.comap_nhds_within, set.preimage_compl],
  congr, ext, exact hf.inj.eq_iff
end

.
lemma Scheme.hom.quasi_finite_at_iff_is_open {x : X.carrier} : 
  f.quasi_finite_at x ↔ is_open ({f.as_fiber x} : set (f.fiber $ f.1.base x).carrier) :=
begin
  change 𝓝[{ y | f.1.base y = f.1.base x } ∩ {x}ᶜ] x = ⊥ ↔ _,
  transitivity is_open (f.fiber_carrier (f.1.base x) '' {f.as_fiber x}),
  { rw [set.image_singleton, ← is_isolated_point_iff, set.inter_comm,
    nhds_within_inter', ← filter.subtype_coe_map_comap, filter.map_eq_bot_iff,
    ← embedding_subtype_coe.comap_nhds_within_ne, f.fiber_carrier_as_fiber] },
  { exact (open_embedding.open_iff_image_open $ homeomorph.open_embedding _).symm }
end

lemma Scheme.hom.quasi_finite_at_tfae [locally_of_finite_type f] (x : X.carrier) : 
  tfae [f.quasi_finite_at x,
    is_open ({f.as_fiber x} : set (f.fiber $ f.1.base x).carrier),
    is_clopen ({f.as_fiber x} : set (f.fiber $ f.1.base x).carrier),
    (PresheafedSpace.stalk_map (f.fiber_to_residue_field (f.1.base x)).1 $ f.as_fiber x).finite,
    is_closed ({f.as_fiber x} : set (f.fiber $ f.1.base x).carrier) ∧
      stable_under_generalization ({f.as_fiber x} : set (f.fiber $ f.1.base x).carrier)] :=
begin
  rw list.tfae_cons_cons,
  split, { exact f.quasi_finite_at_iff_is_open },
  exact @is_open_singleton_tfae (f.fiber (f.1.base x))
    (local_ring.residue_field (Y.presheaf.stalk $ f.1.base x)) _
    (f.fiber_to_residue_field (f.1.base x))
    (category_theory.limits.pullback.snd.locally_of_finite_type _ _)
    (f.as_fiber x)
end

@[mk_iff]
class locally_quasi_finite extends locally_of_finite_type f : Prop :=
(quasi_finite_at : ∀ x, f.quasi_finite_at x)

lemma locally_quasi_finite_iff_fiber {f : X ⟶ Y} [locally_of_finite_type f] :
  locally_quasi_finite f ↔ ∀ y, discrete_topology (f.fiber y).carrier :=
begin
  simp_rw [discrete_topology_iff_forall_is_open_singleton, locally_quasi_finite_iff,
    and_iff_right ‹locally_of_finite_type f›, f.quasi_finite_at_iff_is_open],
  split,
  { intros H x y,
    have := H (f.fiber_carrier _ y),
    rwa [f.as_fiber_fiber_carrier, ← set.image_singleton,
      ← open_embedding.open_iff_image_open] at this,
    exact (Top.homeo_of_iso $
      Scheme.forget_to_Top.map_iso $ as_iso $ f.fiber_congr _).open_embedding },
  { intros H x, apply H }
end

instance locally_quasi_finite.discrete_fiber [locally_quasi_finite f] (y : Y.carrier) :
  discrete_topology (f.fiber y).carrier :=
locally_quasi_finite_iff_fiber.mp ‹locally_quasi_finite f› y

noncomputable
def _root_.category_theory.limits.pullback.map_iso {C} [category C] {X Y Z X' Y' Z' : C}
  (f : X ⟶ Z) (g : Y ⟶ Z) (f' : X' ⟶ Z') (g' : Y' ⟶ Z') (i₁ : X ≅ X')
  (i₂ : Y ≅ Y') (i₃ : Z ≅ Z') (h₁ : f ≫ i₃.hom = i₁.hom ≫ f')
  (h₂ : g ≫ i₃.hom = i₂.hom ≫ g') [limits.has_pullback f g] [limits.has_pullback f' g'] :
  limits.pullback f g ≅ limits.pullback f' g' :=
{ hom := limits.pullback.map f g f' g' i₁.hom i₂.hom i₃.hom h₁ h₂,
  inv := limits.pullback.map f' g' f g i₁.inv i₂.inv i₃.inv
    (by rw [iso.comp_inv_eq, category.assoc, h₁, iso.inv_hom_id_assoc])
    (by rw [iso.comp_inv_eq, category.assoc, h₂, iso.inv_hom_id_assoc]),
  hom_inv_id' := by { ext; simp },
  inv_hom_id' := by { ext; simp } }
.
open _root_.category_theory.limits

noncomputable
def fiber_fst_iso_pullback_fiber {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) (x : X.carrier) :
  (limits.pullback.fst : limits.pullback f g ⟶ _).fiber x ≅
    limits.pullback (g.fiber_to_residue_field (f.1.base x))
      (Scheme.Spec.map $ (f.map_residue_field x).op) :=
begin
  delta Scheme.hom.fiber Scheme.hom.fiber_ι,
  refine pullback_symmetry _ _ ≪≫ pullback_right_pullback_fst_iso _ _ _ ≪≫
    pullback.congr_hom (f.map_residue_field_from_Spec_residue_field x).symm rfl ≪≫ 
    (pullback_right_pullback_fst_iso _ _ _).symm ≪≫ pullback_symmetry _ _ ≪≫ 
    pullback.map_iso _ _ _ _ (pullback_symmetry _ _) (iso.refl _) (iso.refl _) _ _,
  { simp only [iso.refl_hom, category.comp_id, Scheme.hom.fiber_to_residue_field,
      pullback_symmetry_hom_comp_snd] },
  { simp only [iso.refl_hom, category.comp_id, category.id_comp] },
end

lemma Scheme.hom.quasi_finite_at.comp {X Y Z : Scheme} {f : X ⟶ Y} {g : Y ⟶ Z}
  {x : X.carrier} (hf : f.quasi_finite_at x) (hg : g.quasi_finite_at (f.1.base x)) :
  (f ≫ g).quasi_finite_at x :=
begin
  delta Scheme.hom.quasi_finite_at at hf hg ⊢,
  rw [eq_bot_iff, ← hf],
  refine le_inf inf_le_left (le_of_le_of_eq _ sup_bot_eq),
  rw [← @filter.comap_bot _ _ f.1.base, ← hg, nhds_within, nhds_within, filter.comap_inf,
    filter.comap_principal, sup_inf_left, filter.sup_principal],
  refine le_inf (inf_le_left.trans (le_trans _ le_sup_right)) (inf_le_right.trans _),
  { rw ← filter.tendsto_iff_comap, exact f.1.base.2.continuous_at },
  { rw filter.principal_mono, intros y hy,
    by_cases f.1.base y = f.1.base x, exacts [or.inl ⟨h, hy.2⟩, or.inr ⟨hy.1, h⟩] }
end

lemma Scheme.hom.quasi_finite_at.of_comp {X Y Z : Scheme} {f : X ⟶ Y} {g : Y ⟶ Z}
  {x : X.carrier} (h : (f ≫ g).quasi_finite_at x) :
  f.quasi_finite_at x :=
begin
  delta Scheme.hom.quasi_finite_at at h ⊢,
  simp_rw [eq_bot_iff, ← h, Scheme.comp_val_base, coe_comp],
  exact nhds_within_mono _ (λ x h, ⟨(congr_arg g.1.base h.1 : _), h.2⟩),
end

lemma Scheme.hom.quasi_finite_at.iff_comp {X Y Z : Scheme} {f : X ⟶ Y} {g : Y ⟶ Z}
  {x : X.carrier} (hg : g.quasi_finite_at (f.1.base x)) :
  (f ≫ g).quasi_finite_at x ↔ f.quasi_finite_at x :=
⟨Scheme.hom.quasi_finite_at.of_comp, λ h, Scheme.hom.quasi_finite_at.comp h hg⟩

lemma locally_quasi_finite_stable_under_composition :
  morphism_property.stable_under_composition @locally_quasi_finite :=
λ X Y Z f g hf hg, by exactI ⟨λ x, Scheme.hom.quasi_finite_at.comp (hf.2 _) (hg.2 _)⟩

lemma locally_quasi_finite_of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  (hfg : locally_quasi_finite (f ≫ g)) : locally_quasi_finite f :=
@@locally_quasi_finite.mk (locally_of_finite_type_of_comp f g)
  (λ x, Scheme.hom.quasi_finite_at.of_comp (hfg.2 x))

lemma Scheme.hom.quasi_finite_at.of_injective
  (hf : function.injective f.1.base) (x) : f.quasi_finite_at x :=
begin
  rw [Scheme.hom.quasi_finite_at, eq_bot_iff, nhds_within],
  refine inf_le_right.trans_eq (filter.principal_eq_bot_iff.mpr _),
  rw set.eq_empty_iff_forall_not_mem,
  rintro y ⟨h₁, h₂⟩, exact h₂ (hf h₁)
end

lemma locally_quasi_finite_of_mono [mono f] [locally_of_finite_type f] :
  locally_quasi_finite f :=
⟨f^.quasi_finite_at.of_injective (injective_of_mono f)⟩

lemma locally_quasi_finite_respects_iso : 
  morphism_property.respects_iso @locally_quasi_finite :=
locally_quasi_finite_stable_under_composition.respects_iso
  (λ X Y e, locally_quasi_finite_of_mono e.hom)

lemma locally_quasi_finite_stable_under_base_change : 
  morphism_property.stable_under_base_change @locally_quasi_finite :=
morphism_property.stable_under_base_change.mk locally_quasi_finite_respects_iso
begin
  introsI X Y S f g H,
  rw locally_quasi_finite_iff_fiber,
  intro y,
  refine @@open_embedding.discrete_topology _ _ _ (Top.homeo_of_iso (Scheme.forget_to_Top.map_iso $
    fiber_fst_iso_pullback_fiber f g y)).open_embedding (show _, from _),
  apply_with discrete_topology_pullback_carrier_of_finite_type { instances := ff },
  { delta Scheme.hom.fiber_to_residue_field, apply_instance },
  { apply_instance }
end

instance locally_quasi_finite_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [locally_quasi_finite f] [locally_quasi_finite g] : locally_quasi_finite (f ≫ g) :=
locally_quasi_finite_stable_under_composition _ _ infer_instance infer_instance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [locally_quasi_finite g] :
  locally_quasi_finite (pullback.fst : pullback f g ⟶ X) :=
locally_quasi_finite_stable_under_base_change (is_pullback.of_has_pullback f g).flip infer_instance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [locally_quasi_finite f] :
  locally_quasi_finite (pullback.snd : pullback f g ⟶ Y) :=
locally_quasi_finite_stable_under_base_change (is_pullback.of_has_pullback f g) infer_instance

local notation `𝖲𝗉𝖾𝖼` K := Scheme.Spec.obj (op $ CommRing.of $ K)

lemma finite_of_quasi_finite {K : Type*} [field K] (f : X ⟶ 𝖲𝗉𝖾𝖼 K)
  [locally_quasi_finite f] [quasi_compact f] : finite f :=
begin
  rw (finite_tfae_of_finite_type f).out 3 1,
  refine ((f.fiber_carrier (show prime_spectrum K, from ⊥)).trans ((homeomorph.set_congr _).trans
    (homeomorph.set.univ X.carrier))).symm.open_embedding.discrete_topology,
  exact set.eq_univ_iff_forall.mpr (λ x, @subsingleton.elim (prime_spectrum K) _ _ _)
end

lemma quasi_finite_tfae (f : X ⟶ Y) [locally_of_finite_type f] [quasi_compact f] :
  tfae [locally_quasi_finite f,
    ∀ x, _root_.finite (f.fiber x).carrier,
    ∀ x, finite (f.fiber_to_residue_field x),
    ∀ (K : Type u) [field K], by exactI ∀ (g : Scheme.Spec.obj (op $ CommRing.of K) ⟶ Y),
      finite (limits.pullback.snd : limits.pullback f g ⟶ _)] :=
begin
  have := λ x, @finite_tfae_of_finite_type (f.fiber x) _ _
    (f.fiber_to_residue_field x)
    (category_theory.limits.pullback.snd.locally_of_finite_type _ _)
    (category_theory.limits.pullback.snd.quasi_compact _ _),
  tfae_have : 1 → 4, { introsI, exact finite_of_quasi_finite _ },
  tfae_have : 4 → 3, { intros H x, apply H },
  tfae_have : 3 ↔ 2, { exact forall_congr (λ x, (this x).out 3 0) },
  tfae_have : 2 ↔ 1,
  { exact (forall_congr (λ x, (this x).out 0 1)).trans locally_quasi_finite_iff_fiber.symm },
  tfae_finish,
end

instance locally_quasi_finite.finite_fiber [locally_quasi_finite f] [quasi_compact f]
  (y : Y.carrier) :
  _root_.finite (f.fiber y).carrier :=
let H := (quasi_finite_tfae f).out 0 1 in H.mp infer_instance y

lemma locally_quasi_finite.set_finite_fiber [locally_quasi_finite f] [quasi_compact f]
  (y : Y.carrier) : { x | f.1.base x = y }.finite :=
begin
  apply_with set.to_finite { instances := ff },
  exact (f.fiber_carrier y).finite_iff.mp (locally_quasi_finite.finite_fiber f y),
end

instance finite.to_locally_quasi_finite [finite f] : locally_quasi_finite f :=
by { rw (quasi_finite_tfae f).out 0 3, intros, apply_instance }

instance is_immersion.to_locally_quasi_finite [is_immersion f] : locally_quasi_finite f :=
locally_quasi_finite_of_mono f

lemma Scheme.hom.quasi_finite_at.of_comp_is_open_immersion {X Y Z : Scheme} {f : X ⟶ Y}
  {g : Y ⟶ Z} [is_open_immersion f] {x : X.carrier} (h : (f ≫ g).quasi_finite_at x) : 
  g.quasi_finite_at (f.1.base x) :=
begin
  delta Scheme.hom.quasi_finite_at at h ⊢,
  simp_rw [Scheme.comp_val_base, coe_comp] at h,
  rw [eq_bot_iff, ← @filter.map_bot _ _ f.1.base, ← h,
    (is_immersion.base_embedding f).map_nhds_within_eq, ← nhds_within_inter_of_mem],
  show set.range f.1.base ∈ nhds_within _ _,
  { apply nhds_within_le_nhds,
    exact is_open.mem_nhds (is_open_immersion.base_open f).2 (set.mem_range_self x) },
  apply nhds_within_mono,
  rintros _ ⟨⟨y, rfl⟩, h₁, h₂⟩,
  exact ⟨_, ⟨h₁, λ e, h₂ (congr_arg f.1.base e)⟩, rfl⟩,
end

lemma locally_quasi_finite_is_local_at_source : 
  property_is_local_at_source @locally_quasi_finite :=
begin
  refine ⟨locally_quasi_finite_respects_iso, _, _⟩,
  { introsI, apply_instance },
  { introsI X Y f 𝒰 H,
    refine @@locally_quasi_finite.mk
      (locally_of_finite_type_is_local_at_source.3 f 𝒰 infer_instance) _,
    intro x,
    obtain ⟨y, hy⟩ := 𝒰.covers x,
    exact hy ▸ ((H $ 𝒰.f x).2 y).of_comp_is_open_immersion }
end

lemma locally_quasi_finite_is_local_at_target : 
  property_is_local_at_target @locally_quasi_finite :=
begin
  refine ⟨locally_quasi_finite_respects_iso, _, _⟩,
  { introsI, delta morphism_restrict, apply_instance },
  { introsI X Y f 𝒰 H,
    apply locally_quasi_finite_is_local_at_source.3 f (𝒰.pullback_cover f),
    intro i,
    rw [Scheme.open_cover.pullback_cover_map, pullback.condition],
    apply_instance }
end

end algebraic_geometry