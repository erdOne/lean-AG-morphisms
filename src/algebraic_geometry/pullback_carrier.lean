import algebraic_geometry.points

open opposite topological_space category_theory category_theory.limits

noncomputable theory

namespace algebraic_geometry

namespace pullback

universe u

variables {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)

structure triplet :=
(x : X.carrier)
(y : Y.carrier)
(z : Z.carrier)
(hx : f.1.base x = z)
(hy : g.1.base y = z)
.
variables {f g} (T : triplet f g)

def triplet.residue_field_tensor : CommRing :=
pushout (Z.residue_field_of_eq T.hx ≫ f.map_residue_field T.x)
        (Z.residue_field_of_eq T.hy ≫ g.map_residue_field T.y)
.
def triplet.Spec_residue_field_tensor_to :
  Scheme.Spec.obj (op T.residue_field_tensor) ⟶ pullback f g :=
pullback.lift (Scheme.Spec.map pushout.inl.op ≫ X.from_Spec_residue_field T.x)
              (Scheme.Spec.map pushout.inr.op ≫ Y.from_Spec_residue_field T.y)
begin
  have := @pushout.condition _ _ _ _ _ (Z.residue_field_of_eq T.hx ≫ f.map_residue_field T.x)
    (Z.residue_field_of_eq T.hy ≫ g.map_residue_field T.y) _,
  replace this := congr_arg (λ f, Z.residue_field_of_eq T.hx.symm ≫ f) this,
  simp only [category.assoc, Scheme.residue_field_of_eq_trans_assoc,
    Scheme.residue_field_of_eq_refl, category.id_comp] at this,
  simp only [category.assoc, ← Scheme.hom.map_residue_field_from_Spec_residue_field,
    ← Scheme.Spec.map_comp_assoc, ← op_comp, this],
  rw [op_comp, functor.map_comp_assoc],
  congr' 1,
  generalize_proofs h,
  revert h,
  rw [T.hx, T.hy],
  simp only [Scheme.residue_field_of_eq_refl, category.id_comp, op_id,
    category_theory.functor.map_id, category.id_comp, eq_self_iff_true, forall_true_left]
end

@[simps]
def triplet_of_pullback (t : (pullback f g).carrier) : triplet f g :=
{ x := (pullback.fst : pullback f g ⟶ X).1.base t,
  y := (pullback.snd : pullback f g ⟶ Y).1.base t,
  z := (limit.π _ walking_cospan.one : pullback f g ⟶ Z).1.base t,
  hx := by { rw [limit.π, pullback_cone.condition_one (limit.cone (cospan f g))], refl },
  hy := by { rw [limit.π, pullback_cone.condition_one (limit.cone (cospan f g)),
    pullback_cone.condition], refl } }

.
def residue_field_tensor_of_pullback_to (t : (pullback f g).carrier) :
  (triplet_of_pullback t).residue_field_tensor ⟶ Scheme.residue_field _ t :=
pushout.desc
  ((pullback.fst : pullback f g ⟶ _).map_residue_field t)
  ((pullback.snd : pullback f g ⟶ _).map_residue_field t)
begin
  dsimp only [triplet_of_pullback_x, triplet_of_pullback_y],
  rw [category.assoc, category.assoc, ← Scheme.hom.map_residue_field_comp,
    ← Scheme.hom.map_residue_field_comp, Scheme.hom.map_residue_field_congr pullback.condition,
    Scheme.residue_field_of_eq_trans_assoc],
  refl
end

def residue_field_tensor_prime_ideal (t : (pullback f g).carrier) :
  prime_spectrum (triplet_of_pullback t).residue_field_tensor :=
prime_spectrum.comap (residue_field_tensor_of_pullback_to t) ⊥

lemma Spec_residue_field_tensor_of_pullback_to_comp (t : (pullback f g).carrier) :
  Scheme.Spec.map (residue_field_tensor_of_pullback_to t).op ≫
    (triplet_of_pullback t).Spec_residue_field_tensor_to =
    Scheme.from_Spec_residue_field _ t :=
begin
  apply pullback.hom_ext,
  { rw [category.assoc, triplet.Spec_residue_field_tensor_to, pullback.lift_fst,
      ← functor.map_comp_assoc, ← op_comp, residue_field_tensor_of_pullback_to,
      pushout.inl_desc, ← Scheme.hom.map_residue_field_from_Spec_residue_field], refl },
  { rw [category.assoc, triplet.Spec_residue_field_tensor_to, pullback.lift_snd,
      ← functor.map_comp_assoc, ← op_comp, residue_field_tensor_of_pullback_to,
      pushout.inr_desc, ← Scheme.hom.map_residue_field_from_Spec_residue_field], refl }
end


lemma residue_field_tensor_to_prime_ideal (t : (pullback f g).carrier) :
  (triplet_of_pullback t).Spec_residue_field_tensor_to.val.base
    (residue_field_tensor_prime_ideal t) = t :=
begin
  change (Scheme.Spec.map (residue_field_tensor_of_pullback_to t).op ≫
    (triplet_of_pullback t).Spec_residue_field_tensor_to).1.base _ = t,
  rw [Spec_residue_field_tensor_of_pullback_to_comp, Scheme.from_Spec_residue_field_base],
end

@[ext]
lemma triplet_ext {T₁ T₂ : triplet f g}
  (hx : T₁.x = T₂.x) (hy : T₁.y = T₂.y) : T₁ = T₂ :=
begin
  cases T₁, cases T₂, dsimp only at hx hy, substs hx hy T₁_hx T₂_hx
end

lemma triplet_ext_iff {T₁ T₂ : triplet f g} :
  T₁ = T₂ ↔ T₁.x = T₂.x ∧ T₁.y = T₂.y :=
begin
  split, { rintro rfl, exact ⟨rfl, rfl⟩ }, { intro h, exact triplet_ext h.1 h.2 }
end

def triplet.residue_field_tensor_of_eq {T₁ T₂ : triplet f g} (e : T₁ = T₂) :
  T₁.residue_field_tensor ⟶ T₂.residue_field_tensor :=
pushout.map _ _ _ _
  (X.residue_field_of_eq $ by subst e)
  (Y.residue_field_of_eq $ by subst e)
  (Z.residue_field_of_eq $ by subst e)
  (by { subst e, simp })
  (by { subst e, simp })
.
lemma triplet.residue_field_tensor_of_eq_eq_eq_to_hom
  {T₁ T₂ : triplet f g} (e : T₁ = T₂) :
  triplet.residue_field_tensor_of_eq e = eq_to_hom (by subst e) :=
by { subst e, apply pushout.hom_ext; simpa [triplet.residue_field_tensor_of_eq, -category.comp_id]
  using (category.comp_id _).symm }
.
@[simp, reassoc]
lemma triplet.residue_field_tensor_of_eq_trans
  {T₁ T₂ T₃ : triplet f g} (e : T₁ = T₂) (e' : T₂ = T₃) :
  triplet.residue_field_tensor_of_eq e ≫ triplet.residue_field_tensor_of_eq e' =
    triplet.residue_field_tensor_of_eq (e.trans e') :=
by simp only [triplet.residue_field_tensor_of_eq_eq_eq_to_hom, eq_to_hom_trans]

@[simp]
lemma triplet.residue_field_tensor_of_eq_id {T : triplet f g} :
  triplet.residue_field_tensor_of_eq (refl T) = 𝟙 _ :=
by simp only [triplet.residue_field_tensor_of_eq_eq_eq_to_hom, eq_to_hom_refl]


lemma triplet.of_pullback_tensor_to
  (T : triplet f g) (p : prime_spectrum T.residue_field_tensor) :
  triplet_of_pullback (T.Spec_residue_field_tensor_to.1.base p) = T :=
begin
  ext; dsimp,
  { rw [← Scheme.comp_val_base_apply, triplet.Spec_residue_field_tensor_to,
      pullback.lift_fst, Scheme.comp_val_base_apply, Scheme.from_Spec_residue_field_base] },
  { rw [← Scheme.comp_val_base_apply, triplet.Spec_residue_field_tensor_to,
      pullback.lift_snd, Scheme.comp_val_base_apply, Scheme.from_Spec_residue_field_base] },
end


lemma triplet.eq_from_Spec_residue_field_aux (x : X.carrier) (p) :
  Scheme.Spec.map (X.residue_field_of_eq (Scheme.from_Spec_residue_field_base x p) ≫
    (X.from_Spec_residue_field x).map_residue_field p).op =
  (Scheme.Spec.obj (op (X.residue_field x))).from_Spec_residue_field p :=
begin
  rw ← cancel_mono (X.from_Spec_residue_field x),
  rw [op_comp, functor.map_comp_assoc, Scheme.residue_field_of_eq_from_Spec,
    Scheme.hom.map_residue_field_from_Spec_residue_field],
end

lemma triplet.eq_from_Spec_residue_field (T : triplet f g)
  (p : prime_spectrum T.residue_field_tensor) :
  Scheme.Spec.map (triplet.residue_field_tensor_of_eq (T.of_pullback_tensor_to p).symm ≫
    residue_field_tensor_of_pullback_to _ ≫
    T.Spec_residue_field_tensor_to.map_residue_field p).op =
  Scheme.from_Spec_residue_field _ p :=
begin
  refine eq.trans _ (Scheme.Spec.image_preimage _),
  congr' 1,
  apply quiver.hom.unop_inj,
  apply pushout.hom_ext,
  { have : T.Spec_residue_field_tensor_to ≫ pullback.fst = _ := pullback.lift_fst _ _ _,
    simp only [residue_field_tensor_of_pullback_to,
      triplet.residue_field_tensor_of_eq, quiver.hom.unop_op,
      pushout.inl_desc_assoc, op_comp, category.assoc, unop_comp],
    apply quiver.hom.op_inj,
    apply Scheme.Spec.map_injective,
    rw [← Scheme.hom.map_residue_field_comp, Scheme.hom.map_residue_field_congr this,
      Scheme.residue_field_of_eq_trans_assoc],
    conv_rhs { rw [op_comp, functor.map_comp] },
    rw [quiver.hom.op_unop, functor.image_preimage],
    refine eq.trans _ (Scheme.hom.map_residue_field_from_Spec_residue_field _ _),
    rw [Scheme.hom.map_residue_field_comp, ← category.assoc, op_comp, functor.map_comp,
      ← triplet.eq_from_Spec_residue_field_aux],
    refl },
  { have : T.Spec_residue_field_tensor_to ≫ pullback.snd = _ := pullback.lift_snd _ _ _,
    simp only [residue_field_tensor_of_pullback_to,
      triplet.residue_field_tensor_of_eq, quiver.hom.unop_op,
      pushout.inr_desc_assoc, op_comp, category.assoc, unop_comp],
    apply quiver.hom.op_inj,
    apply Scheme.Spec.map_injective,
    rw [← Scheme.hom.map_residue_field_comp, Scheme.hom.map_residue_field_congr this,
      Scheme.residue_field_of_eq_trans_assoc],
    conv_rhs { rw [op_comp, functor.map_comp] },
    rw [quiver.hom.op_unop, functor.image_preimage],
    refine eq.trans _ (Scheme.hom.map_residue_field_from_Spec_residue_field _ _),
    rw [Scheme.hom.map_residue_field_comp, ← category.assoc, op_comp, functor.map_comp,
      ← triplet.eq_from_Spec_residue_field_aux],
    refl },
end
.
lemma carrier_equiv_eq
  {T₁ T₂ : Σ T : triplet f g, prime_spectrum T.residue_field_tensor} :
  T₁ = T₂ ↔ ∃ e : T₁.1 = T₂.1, prime_spectrum.comap
    (triplet.residue_field_tensor_of_eq e.symm) T₁.2 = T₂.2 :=
begin
  split,
  { rintro rfl, refine ⟨rfl, _⟩, rw triplet.residue_field_tensor_of_eq_id, ext, refl },
  { cases T₁, cases T₂, dsimp, rintro ⟨rfl, rfl⟩, congr' 1,
    rw triplet.residue_field_tensor_of_eq_id, ext, refl }
end

variables (f g)

def carrier_equiv :
  (pullback f g).carrier ≃ Σ T : triplet f g, prime_spectrum T.residue_field_tensor :=
{ to_fun := λ t, ⟨_, residue_field_tensor_prime_ideal t⟩,
  inv_fun := λ T, T.1.Spec_residue_field_tensor_to.1.base T.2,
  left_inv := residue_field_tensor_to_prime_ideal,
  right_inv :=
  begin
    rintro ⟨T, p⟩,
    apply carrier_equiv_eq.mpr ⟨_, _⟩; dsimp,
    { ext; dsimp only [triplet_of_pullback_x, triplet_of_pullback_y],
      { rw [← Scheme.comp_val_base_apply, triplet.Spec_residue_field_tensor_to,
          pullback.lift_fst, Scheme.comp_val_base_apply, Scheme.from_Spec_residue_field_base] },
      { rw [← Scheme.comp_val_base_apply, triplet.Spec_residue_field_tensor_to,
          pullback.lift_snd, Scheme.comp_val_base_apply, Scheme.from_Spec_residue_field_base] } },
    { delta residue_field_tensor_prime_ideal,
      have : prime_spectrum.comap (T.Spec_residue_field_tensor_to.map_residue_field p) ⊥ = ⊥ :=
        subsingleton.elim _ _,
      rw [← this, ← prime_spectrum.comap_comp_apply, ← prime_spectrum.comap_comp_apply],
      convert_to
        (Scheme.Spec.map (triplet.residue_field_tensor_of_eq _ ≫
          residue_field_tensor_of_pullback_to _ ≫
          T.Spec_residue_field_tensor_to.map_residue_field p).op).1.base _ = p,
      rw [triplet.eq_from_Spec_residue_field, Scheme.from_Spec_residue_field_base] }
  end }
.
instance {K M N : Type*} [field K] [add_comm_group M] [add_comm_group N] [module K M] [module K N]
  [nontrivial M] [nontrivial N] : nontrivial (tensor_product K M N) :=
begin
  obtain ⟨v, ⟨hv⟩⟩ := basis.exists_basis K M,
  obtain ⟨w, ⟨hw⟩⟩ := basis.exists_basis K N,
  haveI := hv.index_nonempty,
  haveI := hw.index_nonempty,
  exact ⟨⟨_, _, (hv.tensor_product hw).ne_zero (classical.arbitrary _)⟩⟩
end

lemma CommRing.pushout_nontrivial {A B C : CommRing.{u}} (hA : is_field A) (f : A ⟶ B) (g : A ⟶ C)
  [nontrivial B] [nontrivial C] : nontrivial.{u} (pushout f g : _) :=
begin
  delta pushout,
  apply_with (@@equiv.nontrivial (colimit.iso_colimit_cocone ⟨_, CommRing.pushout_cocone_is_colimit
    f g⟩).CommRing_iso_to_ring_equiv.to_equiv) { instances := ff },
  dsimp,
  letI := hA.to_field, letI := f.to_algebra, letI := g.to_algebra,
  apply_instance,
end

instance {R : Type*} [comm_ring R] [nontrivial R] : nonempty (prime_spectrum R) :=
⟨⟨_, (ideal.exists_maximal R).some_spec.is_prime⟩⟩

variables {f g}

lemma triplet.exists_preimage (T : triplet f g) :
  ∃ t : (pullback f g).carrier,
    (pullback.fst : _ ⟶ X).1.base t = T.x ∧ (pullback.snd : _ ⟶ Y).1.base t = T.y :=
begin
  haveI : nontrivial T.residue_field_tensor,
  { delta triplet.residue_field_tensor,
    exact CommRing.pushout_nontrivial (field.to_is_field (Z.residue_field T.z)) _ _ },
  obtain ⟨t, ht⟩ := (carrier_equiv f g).surjective ⟨T, classical.arbitrary _⟩,
  rw (show T = ((carrier_equiv f g) t).1, by rw ht),
  exact ⟨t, rfl, rfl⟩,
end

lemma range_fst :
  set.range (pullback.fst : pullback f g ⟶ X).1.base = f.1.base ⁻¹' set.range g.1.base :=
begin
  apply le_antisymm,
  { rintro _ ⟨y, rfl⟩,
    refine ⟨(pullback.snd : pullback f g ⟶ Y).1.base y, _⟩,
    rw [← Scheme.comp_val_base_apply, ← Scheme.comp_val_base_apply, pullback.condition] },
  { rintro x ⟨y, hxy⟩,
    obtain ⟨t, rfl : _ = x, -⟩ := triplet.exists_preimage ⟨x, y, _, hxy.symm, rfl⟩,
    exact ⟨_, rfl⟩ }
end

lemma range_snd :
  set.range (pullback.snd : pullback f g ⟶ Y).1.base = g.1.base ⁻¹' set.range f.1.base :=
begin
  apply le_antisymm,
  { rintro _ ⟨y, rfl⟩,
    refine ⟨(pullback.fst : pullback f g ⟶ X).1.base y, _⟩,
    rw [← Scheme.comp_val_base_apply, ← Scheme.comp_val_base_apply, pullback.condition] },
  { rintro x ⟨y, hxy⟩,
    obtain ⟨t, -, rfl : _ = x⟩ := triplet.exists_preimage ⟨y, x, _, hxy, rfl⟩,
    exact ⟨_, rfl⟩ }
end

lemma range_to_base :
    set.range (pullback.fst ≫ f : pullback f g ⟶ Z).1.base =
      set.range f.1.base ∩ set.range g.1.base :=
begin
  apply le_antisymm,
  { rintro _ ⟨x, rfl⟩,
    refine ⟨⟨_, rfl⟩, _⟩,
    rw pullback.condition,
    exact ⟨_, rfl⟩ },
  { rintro z ⟨⟨x, hx⟩, ⟨y, hy⟩⟩,
    obtain ⟨t, ht : _ = x, -⟩ := triplet.exists_preimage ⟨x, y, z, hx, hy⟩,
    substs hx ht,
    exact ⟨_, rfl⟩ }
end

lemma range_map {X Y S X' Y' S' : Scheme} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S')
  (g' : Y' ⟶ S') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f')
  (e₂ : g ≫ i₃ = i₂ ≫ g') [mono i₃] :
  set.range (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂).1.base = 
  (pullback.fst : pullback f' g' ⟶ X').val.base ⁻¹' set.range i₁.val.base ∩
  (pullback.snd : pullback f' g' ⟶ Y').val.base ⁻¹' set.range i₂.val.base :=
begin
  simp only [pullback_map_eq_pullback_fst_fst_iso_inv, Scheme.comp_val_base, coe_comp],
  rw [set.range_comp, set.range_iff_surjective.mpr _, set.image_comp, set.image_univ,
    range_snd, set.image_preimage_eq_inter_range, range_fst, range_fst],
  exact (as_iso $ (Scheme.forget_to_Top ⋙ forget Top).map
    (pullback_fst_fst_iso f g f' g' i₁ i₂ i₃ e₁ e₂).inv).to_equiv.surjective,
end

end pullback

end algebraic_geometry