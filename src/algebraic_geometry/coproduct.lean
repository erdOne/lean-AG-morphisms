import algebraic_geometry.limits 
import algebraic_geometry.misc
import category_theory.limits.preserves.opposites

universes u v

open category_theory category_theory.limits topological_space

namespace algebraic_geometry

variables {J : Type u} [decidable_eq J] (X : J → Scheme.{u})

lemma comp_eq_of_is_initial {C : Type*} [category C] [has_strict_initial_objects C] 
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hY : is_initial Y) : f ≫ g = h :=
by { haveI := hY.is_iso_to f, rw ← is_iso.eq_inv_comp, exact hY.hom_ext _ _ }

@[simps]
noncomputable
def coproduct_glue_data : Scheme.glue_data :=
{ J := J,
  U := X,
  V := λ ij, if ij.1 = ij.2 then X ij.1 else ∅,
  f := λ i j, if h : i = j then eq_to_hom (if_pos h) else eq_to_hom (if_neg h) ≫ (X i).empty_to,
  f_mono := λ i j, by split_ifs; apply_instance,
  f_id := λ i, by { rw dif_pos rfl, apply_instance },
  t := λ i j, eq_to_hom (by { dsimp only, simp_rw @eq_comm _ i j, split_ifs, subst h, refl }),
  t_id := λ i, eq_to_hom_refl _ _,
  t' := λ i j k, if h₁ : i = j then if h₂ : j = k then eq_to_hom (by substs h₁ h₂)
      else pullback.snd ≫ eq_to_hom (by { subst h₁, exact dif_neg h₂ }) ≫ Scheme.empty_to _
      else pullback.fst ≫ eq_to_hom (dif_neg h₁) ≫ Scheme.empty_to _,
  t_fac := begin
    intros i j k,
    dsimp only,
    split_ifs with h₁,
    { subst h₁, rw [eq_to_hom_refl, category.comp_id],
      by_cases h₂ : i = k,
      { subst h₂, simp only [dif_pos rfl, eq_to_hom_refl, category.id_comp],
        rw ← cancel_mono (eq_to_hom (show ite (i = i) (X i) ∅ = X i, from dif_pos rfl)),
        convert pullback.condition.symm; rw dif_pos rfl; refl },
      { simp only [dif_neg h₂],
        rw [← category.assoc, category.assoc],
        exact comp_eq_of_is_initial _ _ _ is_initial_of_is_empty } },
    { rw [← category.assoc, category.assoc],
      exact comp_eq_of_is_initial _ _ _ is_initial_of_is_empty }
  end,
  cocycle := begin
    intros i j k,
    dsimp only,
    split_ifs with h₁,
    { subst h₁,
      by_cases h₂ : i = k,
      { subst h₂, simp only [dif_pos rfl, eq_to_hom_refl, category.id_comp] },
      { simp only [dif_neg h₂, category.assoc],
        rw ← category.assoc, exact comp_eq_of_is_initial _ _ _ is_initial_of_is_empty } },
    { simp only [category.assoc],
      rw ← category.assoc, exact comp_eq_of_is_initial _ _ _ is_initial_of_is_empty }
  end,
  f_open := λ i j, by { dsimp only at *, split_ifs; apply_instance } }
.

noncomputable
def multicoequalizer_is_coproduct_of_is_initial
  {C : Type*} [category C] (I : multispan_index C) [has_multicoequalizer I]
  (hI : ∀ i, (∃ h : I.fst_from i = I.snd_from i, I.fst i = I.snd i ≫ eq_to_hom (by rw h)) ∨
    nonempty (is_initial (I.left i))) :
  is_colimit (cofan.mk (multicoequalizer I) (multicoequalizer.π I)) :=
{ desc := λ s, multicoequalizer.desc I _ (λ b, s.ι.app ⟨b⟩)
    (by { intro i, rcases hI i with (⟨e₁, e₂⟩|⟨⟨h⟩⟩),
      { rw e₂, generalize_proofs e₃, revert e₃, rw e₁, simp }, { exact h.hom_ext _ _ } }),
  fac' := λ s ⟨j⟩, by rw [cofan.mk_ι_app, multicoequalizer.π_desc],
  uniq' := λ s m H, multicoequalizer.hom_ext I m _
    (λ j, (H ⟨j⟩).trans (multicoequalizer.π_desc I s.X _ _ j).symm) }

noncomputable
def coproduct_glue_data.is_coproduct :
  is_colimit (cofan.mk (coproduct_glue_data X).glued (coproduct_glue_data X).ι) :=
multicoequalizer_is_coproduct_of_is_initial _
begin
  rintro ⟨i, j⟩, dsimp at *, split_ifs,
  exacts [or.inl ⟨h, by simp [dif_pos h.symm]⟩, or.inr ⟨is_initial_of_is_empty⟩]
end

instance : has_coproducts.{u} Scheme :=
λ ι, ⟨λ J, by { classical, exact @@has_colimit_of_iso _ _
  ⟨⟨⟨_, coproduct_glue_data.is_coproduct (J.obj ∘ discrete.mk)⟩⟩⟩ discrete.nat_iso_functor }⟩

noncomputable
def coproduct_glue_data.iso_coproduct : 
  (coproduct_glue_data X).glued ≅ sigma_obj X :=
(colimit.iso_colimit_cocone ⟨_, coproduct_glue_data.is_coproduct X⟩).symm

@[simp, reassoc]
lemma coproduct_glue_data.iso_coproduct_ι_inv (i) : 
  sigma.ι X i ≫ (coproduct_glue_data.iso_coproduct X).inv =
    (coproduct_glue_data X).ι i :=
colimit.iso_colimit_cocone_ι_hom ⟨_, _⟩ ⟨i⟩

@[simp, reassoc]
lemma coproduct_glue_data.iso_coproduct_ι_hom (i) : 
  (coproduct_glue_data X).ι i ≫ (coproduct_glue_data.iso_coproduct X).hom =
    sigma.ι X i :=
colimit.iso_colimit_cocone_ι_inv ⟨_, coproduct_glue_data.is_coproduct X⟩ ⟨i⟩

instance (i) : is_open_immersion (sigma.ι X i) :=
begin
  rw ← coproduct_glue_data.iso_coproduct_ι_hom,
  apply_instance
end

lemma sigma_ι_jointly_surjective (x : (∐ X).carrier) : 
  ∃ i, x ∈ set.range (sigma.ι X i : _).1.base :=
begin
  obtain ⟨i, y, e⟩ := (coproduct_glue_data X).ι_jointly_surjective
    ((coproduct_glue_data.iso_coproduct X).inv.1.base x),
  refine ⟨i, y, _⟩,
  apply (Top.homeo_of_iso $ Scheme.forget_to_Top.map_iso $
    coproduct_glue_data.iso_coproduct X).symm.injective,
  change (sigma.ι X i ≫ (coproduct_glue_data.iso_coproduct X).inv).1.base y = _,
  rwa coproduct_glue_data.iso_coproduct_ι_inv,
end

lemma supr_opens_range_sigma_ι : (⨆ i, Scheme.hom.opens_range (sigma.ι X i)) = ⊤ :=
begin
  rw eq_top_iff,
  rintro x -,
  rw [opens.coe_supr, set.mem_Union],
  exact sigma_ι_jointly_surjective X x
end

lemma is_open_immersion_of_open_cover {X Y : Scheme} (f : X ⟶ Y) (𝒰 : X.open_cover)
  [H : ∀ i, is_open_immersion (𝒰.map i ≫ f)] (hf : function.injective f.1.base) :
  is_open_immersion f :=
begin
  have H' := 𝒰.is_open,
  simp_rw is_open_immersion.iff_stalk_iso at H H' ⊢,
  split,
  { refine open_embedding_iff_continuous_injective_open.mpr ⟨f.1.base.2, hf, λ U hU, _⟩,
    have : (⋃ i, set.range (𝒰.map i).1.base) = set.univ,
    { rw [← opens.coe_top, ← 𝒰.supr_opens_range,
        opens.coe_supr], refl },
    have : f.1.base '' U = ⋃ i, (𝒰.map i ≫ f).1.base '' ((𝒰.map i).1.base ⁻¹' U),
    { simp_rw [Scheme.comp_val_base, coe_comp, set.image_comp f.1.base ((𝒰.map _).1.base),
        set.image_preimage_eq_inter_range, ← set.image_Union, ← set.inter_Union, this,
        set.inter_univ] },
    rw this,
    exact is_open_Union (λ i, (H i).1.is_open_map _ (hU.preimage (𝒰.map i).1.base.2)) },
  { intro x,
    obtain ⟨y, hy⟩ := 𝒰.covers x,
    have := @@is_iso.comp_is_iso _ ((H $ 𝒰.f x).2 y) (@@is_iso.inv_is_iso _ $ (H' (𝒰.f x)).2 y),
    erw [PresheafedSpace.stalk_map.comp, category.assoc, @@is_iso.hom_inv_id,
      category.comp_id] at this,
    rwa ← hy }
end

noncomputable
def is_coproduct_of_is_open_immersion' {Y : Scheme}
  (f : ∀ i, X i ⟶ Y) [H : ∀ i, is_open_immersion (f i)]
  (hf : (⨆ i, (f i).opens_range) = ⊤)
  (hf' : ∀ i j, i ≠ j → disjoint (set.range (f i).1.base) (set.range (f j).1.base)) :
  is_colimit (cofan.mk Y f) :=
begin
  haveI : is_iso (colimit.cocone_morphism (cofan.mk Y f)),
  { apply_with cocones.cocone_iso_of_hom_iso { instances := ff },
    apply_with is_open_immersion.to_iso { instances := ff },
    { apply is_open_immersion_of_open_cover _
        ((Scheme.open_cover_of_is_iso.{u} (coproduct_glue_data.iso_coproduct X).hom).bind
        (λ _, (coproduct_glue_data X).open_cover)),
      { intros x y e,
        obtain ⟨i, x, rfl⟩ := sigma_ι_jointly_surjective X x,
        obtain ⟨j, y, rfl⟩ := sigma_ι_jointly_surjective X y,
        simp_rw [← Scheme.comp_val_base_apply, colimit.cocone_morphism_hom,
          colimit.ι_desc, cofan.mk_ι_app] at e,
        by_cases i = j,
        { subst h, rw (PresheafedSpace.is_open_immersion.base_open).inj e },
        { exact (set.disjoint_iff_forall_ne.mp (hf' _ _ h) _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ e).elim } },
      { rintros ⟨⟨⟩, i⟩, convert H i, delta Scheme.glue_data.open_cover, simp } },
    { rw Top.epi_iff_surjective,
      intro x,
      have : x ∈ (⊤ : opens Y.carrier) := trivial,
      rw [← hf, opens.mem_supr] at this,
      obtain ⟨i, x, rfl⟩ := this,
      refine ⟨(sigma.ι X i : _).1.base x, _⟩,
      rw [← Scheme.comp_val_base_apply, colimit.cocone_morphism_hom, colimit.ι_desc,
        cofan.mk_ι_app] } },
  refine is_colimit.of_iso_colimit (colimit.is_colimit _)
    (as_iso $ colimit.cocone_morphism _),
end

noncomputable
def is_coproduct_of_is_open_immersion {ι : Type u} (X : ι → Scheme.{v}) {Y : Scheme.{v}}
  (f : ∀ i, X i ⟶ Y) [H : ∀ i, is_open_immersion (f i)]
  (hf : (⨆ i, (f i).opens_range) = ⊤)
  (hf' : ∀ i j, i ≠ j → disjoint (set.range (f i).1.base) (set.range (f j).1.base)) :
  is_colimit (cofan.mk Y f) :=
begin
  let s := set.range (λ i, set.range (f i).1.base),
  have : ∀ x : s, x.1 ∈ s := λ x, x.2, choose g hg,
  have hg' : function.injective g,
  { intros x y e, ext1, show x.val = y.val, rw [← hg x, ← hg y, e] },
  let g' : ι → s := λ i, ⟨_, i, rfl⟩,
  have hg₁ : ∀ i, g' (g i) = i := λ i, subtype.ext (hg i),
  have hg₂ : ∀ i, (g' i).1 = ∅ ∨ g (g' i) = i,
  { simp_rw or_iff_not_imp_right, intros i e, simpa only [hg, g', disjoint_self] using hf' _ _ e },
  let f' : ∀ (i : s), X (g i) ⟶ Y := λ i, f _,
  let : is_colimit (cofan.mk Y f'),
  { apply is_coproduct_of_is_open_immersion',
    { simp only [← opens.ext_iff, opens.coe_supr,
        opens.coe_top, Scheme.hom.opens_range_coe, hg,
        set.eq_univ_iff_forall, set.mem_Union] at hf ⊢,
      intro x, obtain ⟨i, hi⟩ := hf x, exact ⟨_, ⟨⟨_, _, rfl⟩, rfl⟩, hi⟩ },
    { exact λ i j e, hf' _ _ (hg'.ne e) } },
  refine ⟨λ c, this.desc ⟨_, discrete.nat_trans (λ i, c.ι.app ⟨_⟩)⟩, _, _⟩,
  { rintros c ⟨i⟩,
    cases hg₂ i,
    { exact (@@is_initial_of_is_empty (set.range_eq_empty_iff.mp h)).hom_ext _ _ },
    { rw eq_comm at h, 
      have e := this.fac ⟨_, discrete.nat_trans (λ i, c.ι.app ⟨_⟩)⟩ ⟨g' i⟩,
      dsimp [cofan.mk_ι_app, f', discrete.nat_trans_app] at e ⊢,
      convert e } },
  { refine λ c m hm, this.uniq ⟨_, discrete.nat_trans (λ i, c.ι.app ⟨_⟩)⟩ _ (λ i, _),
    exact hm ⟨_⟩ }
end

open opposite

lemma bijective_local_ring_hom_fst (R S : Type*) [comm_ring R] [comm_ring S]
  (I : ideal R) [hx : I.is_prime] : 
  function.bijective (localization.local_ring_hom
    (I.comap $ ring_hom.fst R S) I (ring_hom.fst R S) rfl) :=
begin
  split,
  { intros a b e,
    obtain ⟨⟨a₁, a₂⟩, ⟨⟨s₁, s₂⟩, hs⟩, rfl⟩ :=
      is_localization.mk'_surjective (I.comap $ ring_hom.fst R S).prime_compl a,
    obtain ⟨⟨b₁, b₂⟩, ⟨⟨t₁, t₂⟩, ht⟩, rfl⟩ :=
      is_localization.mk'_surjective (I.comap $ ring_hom.fst R S).prime_compl b,
    simp only [localization.local_ring_hom_mk', is_localization.eq, subtype.coe_mk,
      ring_hom.coe_fst] at e ⊢,
    obtain ⟨⟨c, hc⟩, e⟩ := e,
    refine ⟨⟨(c, 0), hc⟩, _⟩,
    simpa using e },
  { intro x,
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ :=
      is_localization.mk'_surjective I.prime_compl x,
    refine ⟨is_localization.mk' _ (x, (1 : S))
      ⟨(s, (1 : S)), show (s, (1 : S)) ∈ (I.comap $ ring_hom.fst R S).prime_compl, from hs⟩, _⟩,
    simp only [localization.local_ring_hom_mk', subtype.coe_mk, ring_hom.coe_fst] }
end

lemma bijective_local_ring_hom_snd (R S : Type*) [comm_ring R] [comm_ring S]
  (I : ideal S) [hx : I.is_prime] : 
  function.bijective (localization.local_ring_hom
    (I.comap $ ring_hom.snd R S) I (ring_hom.snd R S) rfl) :=
begin
  split,
  { intros a b e,
    obtain ⟨⟨a₁, a₂⟩, ⟨⟨s₁, s₂⟩, hs⟩, rfl⟩ :=
      is_localization.mk'_surjective (I.comap $ ring_hom.snd R S).prime_compl a,
    obtain ⟨⟨b₁, b₂⟩, ⟨⟨t₁, t₂⟩, ht⟩, rfl⟩ :=
      is_localization.mk'_surjective (I.comap $ ring_hom.snd R S).prime_compl b,
    simp only [localization.local_ring_hom_mk', is_localization.eq, subtype.coe_mk,
      ring_hom.coe_snd] at e ⊢,
    obtain ⟨⟨c, hc⟩, e⟩ := e,
    refine ⟨⟨(0, c), hc⟩, _⟩,
    simpa using e },
  { intro x,
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ :=
      is_localization.mk'_surjective I.prime_compl x,
    refine ⟨is_localization.mk' _ ((1 : R), x)
      ⟨((1 : R), s), show ((1 : R), s) ∈ (I.comap $ ring_hom.snd R S).prime_compl, from hs⟩, _⟩,
    simp only [localization.local_ring_hom_mk', subtype.coe_mk, ring_hom.coe_snd] }
end

lemma prime_spectrum.range_comap_fst (R S : Type*) [comm_ring R] [comm_ring S] : 
  set.range (prime_spectrum.comap (ring_hom.fst R S)) =
    ↑(prime_spectrum.basic_open ((1, 0) : R × S)) :=
begin
  ext x,
  simp only [set.mem_range, prime_spectrum.basic_open_eq_zero_locus_compl,
    set_like.mem_coe, set.mem_compl_iff, prime_spectrum.mem_zero_locus,
    set.singleton_subset_iff],
  split,
  { rintro ⟨y, rfl⟩, simpa [← ideal.eq_top_iff_one] using y.2.ne_top },
  { rcases (ideal.ideal_prod_prime x.as_ideal).mp x.2 with (⟨p, hp, e⟩|⟨p, hp, e⟩),
    { intro _, refine ⟨⟨p, hp⟩, prime_spectrum.ext.mpr (e.trans _).symm⟩, ext ⟨a, b⟩, simp },
    { rw e, intro h, exact (h ⟨trivial, zero_mem _⟩).elim } }
end

lemma prime_spectrum.range_comap_snd (R S : Type*) [comm_ring R] [comm_ring S] : 
  set.range (prime_spectrum.comap (ring_hom.snd R S)) =
    ↑(prime_spectrum.basic_open ((0, 1) : R × S)) :=
begin
  ext x,
  simp only [set.mem_range, prime_spectrum.basic_open_eq_zero_locus_compl,
    set_like.mem_coe, set.mem_compl_iff, prime_spectrum.mem_zero_locus,
    set.singleton_subset_iff],
  split,
  { rintro ⟨y, rfl⟩, simpa [← ideal.eq_top_iff_one] using y.2.ne_top },
  { rcases (ideal.ideal_prod_prime x.as_ideal).mp x.2 with (⟨p, hp, e⟩|⟨p, hp, e⟩),
    { rw e, intro h, exact (h ⟨zero_mem _, trivial⟩).elim },
    { intro _, refine ⟨⟨p, hp⟩, prime_spectrum.ext.mpr (e.trans _).symm⟩, ext ⟨a, b⟩, simp } }
end

@[instance]
lemma is_open_immersion_Spec_prod_fst {R S : Type u} [comm_ring R] [comm_ring S] : 
  is_open_immersion (Scheme.Spec.map (CommRing.of_hom $ ring_hom.fst R S).op) :=
begin
  apply_with is_open_immersion.of_stalk_iso { instances := ff },
  { refine ⟨(prime_spectrum.closed_embedding_comap_of_surjective _
      (ring_hom.fst R S) prod.fst_surjective).1, _⟩,
    erw prime_spectrum.range_comap_fst,
    exact prime_spectrum.is_open_basic_open },
  { rintro (x : prime_spectrum R),
    erw ← local_ring_hom_comp_stalk_iso,
    apply_with is_iso.comp_is_iso { instances := ff }, { apply_instance },
    apply_with is_iso.comp_is_iso { instances := ff }, swap, { apply_instance },
    rw CommRing.is_iso_iff_bijective,
    convert bijective_local_ring_hom_fst R S x.as_ideal, }
end

@[instance]
lemma is_open_immersion_Spec_prod_snd {R S : Type u} [comm_ring R] [comm_ring S] : 
  is_open_immersion (Scheme.Spec.map (CommRing.of_hom $ ring_hom.snd R S).op) :=
begin
  apply_with is_open_immersion.of_stalk_iso { instances := ff },
  { refine ⟨(prime_spectrum.closed_embedding_comap_of_surjective _
      (ring_hom.snd R S) prod.snd_surjective).1, _⟩,
    erw prime_spectrum.range_comap_snd,
    exact prime_spectrum.is_open_basic_open },
  { rintro (x : prime_spectrum S),
    erw ← local_ring_hom_comp_stalk_iso,
    apply_with is_iso.comp_is_iso { instances := ff }, { apply_instance },
    apply_with is_iso.comp_is_iso { instances := ff }, swap, { apply_instance },
    rw CommRing.is_iso_iff_bijective,
    convert bijective_local_ring_hom_snd R S x.as_ideal, }
end

def binary_cofan_iso_cofan {C : Type*} [category C] {X Y Z : C} 
  (f : X ⟶ Z) (g : Y ⟶ Z) : 
  binary_cofan.mk f g ≅ cofan.mk Z (λ b, walking_pair.cases_on b f g) :=
{ hom := { hom := 𝟙 Z, w' := (by rintro ⟨_|_⟩; dsimp; simp) },
  inv := { hom := 𝟙 Z, w' := (by rintro ⟨_|_⟩; dsimp; simp) },
  hom_inv_id' := by { ext1, dsimp, simp },
  inv_hom_id' := by { ext1, dsimp, simp } }
.

noncomputable
def is_coprod_of_is_open_immersion_of_is_compl {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z)
  [is_open_immersion f] [is_open_immersion g]
    (h : is_compl (set.range f.1.base) (set.range g.1.base)) : 
  is_colimit (binary_cofan.mk f g) :=
begin
  refine is_colimit.of_iso_colimit _ (binary_cofan_iso_cofan _ _).symm,
  fapply is_coproduct_of_is_open_immersion _ _,
  swap 3, { rintros (_|_); dsimp only; apply_instance },
  { ext1, convert h.2.eq_top using 1, rw opens.coe_supr, 
    refine (supr_le _).antisymm (sup_le (le_trans _ $ le_supr _ walking_pair.left)
      (le_trans _ $ le_supr _ walking_pair.right)),
    { rintro (_|_); dsimp only, exacts [le_sup_left, le_sup_right] },
    exacts [le_rfl, le_rfl] },
  { rintro (_|_) (_|_) e; dsimp only, any_goals { exact (e rfl).elim }, exacts [h.1, h.1.symm] }
end

-- set_option trace.class_instances true

noncomputable
def is_coprod_Spec_prod (R S : CommRing.{u}) : 
  is_colimit (binary_cofan.mk
    (Scheme.Spec.map (CommRing.of_hom $ ring_hom.fst R S).op)
    (Scheme.Spec.map (CommRing.of_hom $ ring_hom.snd R S).op)) :=
begin
  apply is_coprod_of_is_open_immersion_of_is_compl _ _,
  rotate,
  { exact is_open_immersion_Spec_prod_fst },
  { exact is_open_immersion_Spec_prod_snd },
  { erw [prime_spectrum.range_comap_fst, prime_spectrum.range_comap_snd],
    split,
    { rw [disjoint_iff, set.inf_eq_inter, ← opens.coe_inf, ← prime_spectrum.basic_open_mul,
        prod.mk_mul_mk, mul_zero, zero_mul, ← prod.zero_eq_mk, prime_spectrum.basic_open_zero,
        set.bot_eq_empty, opens.coe_bot] },
    { have : (1, 0) + (0, 1) = (1 : R × S) := by simp,
      rw [codisjoint_iff, set.sup_eq_union,
        prime_spectrum.basic_open_eq_zero_locus_compl,
        prime_spectrum.basic_open_eq_zero_locus_compl, ← set.compl_inter,
        ← prime_spectrum.zero_locus_union, set.top_eq_univ, compl_eq_comm, set.compl_univ,
        eq_comm, ← prime_spectrum.zero_locus_span, prime_spectrum.zero_locus_empty_iff_eq_top,
        ideal.eq_top_iff_one, ← this],
      refine add_mem (ideal.subset_span _) (ideal.subset_span _),
      exacts [or.inl rfl, or.inr rfl] } }
end

noncomputable
instance Scheme.Spec.preserves_binary_products_right_op
  (R S : CommRing) : preserves_limit (pair R S) Scheme.Spec.{u}.right_op :=
begin
  refine preserves_limit_of_preserves_limit_cone (CommRing.prod_fan_is_limit R S) _,
  refine ((is_limit.postcompose_hom_equiv _ _).symm (is_limit_cone_right_op_of_cocone _ 
    ((is_coprod_Spec_prod R S).whisker_equivalence (discrete.opposite _)))).of_iso_limit _,
  { apply discrete.nat_iso, rintro ⟨_|_⟩; exact iso.refl _ },
  { refine as_iso { hom := (𝟙 _), w' := _ },
    { rintro ⟨_|_⟩; dsimp; rw [category.id_comp, category.comp_id]; refl },
    { exact cones.cone_iso_of_hom_iso _ } }
end
.
noncomputable
instance Scheme.Spec.preserves_binary_coproducts :
  preserves_colimits_of_shape (discrete walking_pair) Scheme.Spec.{u} :=
begin
  apply preserves_colimits_of_shape_of_nat_iso Scheme.Spec.right_op_left_op_iso,
  apply_with preserves_colimits_of_shape_left_op { instances := ff },
  apply preserves_limits_of_shape_of_equiv (discrete.opposite _).symm _,
  constructor,
  intros K,
  apply preserves_limit_of_iso_diagram _ (diagram_iso_pair K).symm,
  exact Scheme.Spec.preserves_binary_products_right_op _ _
end

noncomputable
instance Scheme.Spec.preserves_initial :
  preserves_colimits_of_shape (discrete pempty) Scheme.Spec :=
begin
  apply preserves_colimits_of_shape_pempty_of_preserves_initial _,
  refine preserves_initial_of_iso _ (_ ≪≫ Scheme.Spec.map_iso
    (colimit.iso_colimit_cocone ⟨_, (initial_op_of_terminal CommRing.punit_is_terminal)⟩).symm),
  refine (as_iso $ empty_is_initial.to _).symm ≪≫ _,
  exact (as_iso (empty_is_initial.to (Scheme.Spec.obj (op $ CommRing.of punit))) : _)
end

noncomputable
instance {J : Type} [fintype J] : preserves_colimits_of_shape (discrete J) Scheme.Spec.{u} :=
preserves_finite_coproducts_of_preserves_binary_and_initial _ _

instance : has_finite_coproducts Scheme.{u} :=
has_finite_coproducts_of_has_coproducts.{u u} _

instance {X Y : Scheme.{u}} [is_affine X] [is_affine Y] : is_affine (X ⨿ Y) := 
is_affine_of_iso
  (coprod.map_iso X.iso_Spec Y.iso_Spec ≪≫ preserves_colimit_pair.iso Scheme.Spec _ _).hom



end algebraic_geometry