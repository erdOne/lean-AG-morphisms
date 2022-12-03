import ring_theory.is_tensor_product
import category_theory.limits.shapes.comm_sq
import ring_theory.polynomial.basic
import algebra.category.Ring.constructions

section 
variables (R S : Type*) [comm_ring R] [comm_ring S] [algebra R S] 

open_locale polynomial


@[reducible] noncomputable
def polynomial.polynomial_algebra_of_algebra :
  algebra R[X] S[X] := (polynomial.map_ring_hom $ algebra_map R S).to_algebra

local attribute [instance] polynomial.polynomial_algebra_of_algebra

@[simp]
lemma polynomial.polynomial_algebra_of_algebra_algebra_map_apply (p : R[X]) :
  algebra_map R[X] S[X] p = p.map (algebra_map R S) := rfl

instance polynomial.is_scalar_tower_of_algebra : is_scalar_tower R R[X] S[X] :=
is_scalar_tower.of_algebra_map_eq (λ x, (@polynomial.map_C _ _ x _ _ $ algebra_map R S).symm)

lemma algebra.is_pushout_iff_bijective {R S R' S' : Type*} [comm_ring R] [comm_ring S] 
  [comm_ring R'] [comm_ring S']
  [algebra R S] [algebra R R'] [algebra S S'] [algebra R' S'] [algebra R S']
  [is_scalar_tower R R' S'] [is_scalar_tower R S S'] :
  algebra.is_pushout R R' S S' ↔ function.bijective (algebra.tensor_product.product_map
    (is_scalar_tower.to_alg_hom R R' S')
      (is_scalar_tower.to_alg_hom R S S')) :=
begin
  rw algebra.is_pushout_iff,
  change _ ↔ function.bijective (algebra.tensor_product.product_map _ _).to_linear_map,
  delta is_base_change is_tensor_product,
  congr',
  apply tensor_product.ext',
  intros x y,
  simp only [algebra.of_id_apply,
 tensor_product.lift.tmul,
 alg_hom.to_linear_map_apply,
 linear_map.smul_apply,
 module.algebra_map_End_apply,
 is_scalar_tower.coe_to_alg_hom',
 algebra.smul_def,
 algebra.tensor_product.product_map_apply_tmul,
 linear_map.coe_restrict_scalars_eq_coe,
 linear_map.flip_apply],
end 

lemma algebra.tensor_product.ring_hom_ext {R A B S : Type*} [comm_ring R] [comm_ring A] 
  [comm_ring B] [comm_ring S] [algebra R A] [algebra R B] (f g : tensor_product R A B →+* S) 
    (h : f.comp algebra.tensor_product.include_left.to_ring_hom =
      g.comp algebra.tensor_product.include_left.to_ring_hom)
    (h' : f.comp algebra.tensor_product.include_right.to_ring_hom =
      g.comp algebra.tensor_product.include_right.to_ring_hom) : f = g :=
begin
  ext x,
  induction x using tensor_product.induction_on with x y x y hx hy,
  { rw [map_zero, map_zero] },
  { rw [← mul_one x, ← one_mul y, ← algebra.tensor_product.tmul_mul_tmul,
      map_mul, map_mul],
    congr' 1,
    exacts [(ring_hom.congr_fun h x : _), (ring_hom.congr_fun h' y : _)] },
  { rw [map_add, map_add, hx, hy] }
end 

noncomputable
def tensor_product_polynomial_equiv  :
  tensor_product R S R[X] ≃ₐ[S] S[X] :=
{ inv_fun := (polynomial.eval₂_ring_hom (algebra.tensor_product.include_left.to_ring_hom :
    S →+* tensor_product R S R[X]) (1 ⊗ₜ polynomial.X) : _) ,
  left_inv := begin
    intro x,
    rw [alg_hom.to_fun_eq_coe, ← alg_hom.coe_to_ring_hom, ← ring_hom.comp_apply],
    conv_rhs { rw ← ring_hom.id_apply x },
    congr' 1,
    convert algebra.tensor_product.ring_hom_ext _ (ring_hom.id (tensor_product R S R[X])) _ _,
    { ext x, simp only [algebra.of_id_apply,
 polynomial.eval₂_C,
 mul_one,
 ring_hom_comp_triple.comp_eq,
 algebra.tensor_product.product_left_alg_hom_apply,
  polynomial.polynomial_algebra_of_algebra_algebra_map_apply,
 algebra.id.map_eq_id,
 ring_hom.to_fun_eq_coe,
 ring_hom.id_apply,
 alg_hom.coe_to_ring_hom,
 eq_self_iff_true,
 function.comp_app,
 polynomial.map_one,
 polynomial.coe_eval₂_ring_hom,
 ring_hom.coe_comp,
 is_scalar_tower.coe_to_alg_hom',
 algebra.tensor_product.include_left_apply,
 algebra.tensor_product.product_map_apply_tmul,
 alg_hom.coe_restrict_scalars',
 alg_hom.to_ring_hom_eq_coe,
 polynomial.algebra_map_apply]},
    ext y,
    { suffices : algebra_map R S y ⊗ₜ[R] 1 = 1 ⊗ₜ[R] polynomial.C y, { simpa only [polynomial.map_C,
 polynomial.eval₂_C,
 ring_hom_comp_triple.comp_eq,
 one_mul,
 algebra.tensor_product.product_left_alg_hom_apply,
 polynomial.polynomial_algebra_of_algebra_algebra_map_apply,
 ring_hom.to_fun_eq_coe,
 alg_hom.coe_to_ring_hom,
 function.comp_app,
 map_one,
 algebra.tensor_product.include_right_apply,
 polynomial.coe_eval₂_ring_hom,
 ring_hom.coe_comp,
 is_scalar_tower.coe_to_alg_hom',
 algebra.tensor_product.include_left_apply,
 algebra.tensor_product.product_map_apply_tmul,
 alg_hom.coe_restrict_scalars',
 alg_hom.to_ring_hom_eq_coe] using this },
      rw [algebra.algebra_map_eq_smul_one, tensor_product.smul_tmul,
        ← algebra.algebra_map_eq_smul_one, polynomial.algebra_map_apply], refl },
    { simp only [ring_hom_comp_triple.comp_eq,
 polynomial.map_X,
 one_mul,
 algebra.tensor_product.product_left_alg_hom_apply,
 polynomial.polynomial_algebra_of_algebra_algebra_map_apply,
 polynomial.eval₂_X,
 ring_hom.to_fun_eq_coe,
 alg_hom.coe_to_ring_hom,
 eq_self_iff_true,
 function.comp_app,
 map_one,
 algebra.tensor_product.include_right_apply,
 polynomial.coe_eval₂_ring_hom,
 ring_hom.coe_comp,
 is_scalar_tower.coe_to_alg_hom',
 algebra.tensor_product.product_map_apply_tmul,
 alg_hom.coe_restrict_scalars',
 alg_hom.to_ring_hom_eq_coe] }
  end,
  right_inv := begin
    intro x,
    rw [alg_hom.to_fun_eq_coe, ← alg_hom.coe_to_ring_hom, ← ring_hom.comp_apply],
    conv_rhs { rw ← ring_hom.id_apply x },
    congr' 1,
    ext y; simp only [ alg_hom.coe_restrict_scalars',
 alg_hom.coe_to_ring_hom,
 alg_hom.to_ring_hom_eq_coe,
 algebra.id.map_eq_id,
 algebra.of_id_apply,
 algebra.tensor_product.include_left_apply,
 algebra.tensor_product.product_left_alg_hom_apply,
 algebra.tensor_product.product_map_apply_tmul,
 polynomial.polynomial_algebra_of_algebra_algebra_map_apply,
 function.comp_app,
 is_scalar_tower.coe_to_alg_hom',
 map_one,
 mul_one,
 one_mul,
 polynomial.algebra_map_apply, polynomial.map_X,
 polynomial.coe_eval₂_ring_hom,
 polynomial.eval₂_C,
 polynomial.eval₂_X,
 polynomial.map_one,
 ring_hom.coe_comp,
 ring_hom.id_apply,
 ring_hom.to_fun_eq_coe,
 ring_hom_comp_triple.comp_eq]
  end,
  ..(algebra.tensor_product.product_left_alg_hom (algebra.of_id S S[X])
      (is_scalar_tower.to_alg_hom R R[X] S[X]) : _) }
.
@[instance]
lemma is_pushout_CommRing_polynomial (R S : Type*) [comm_ring R] [comm_ring S] [algebra R S] :
  algebra.is_pushout R S R[X] S[X] :=
begin
  rw algebra.is_pushout_iff_bijective,
  exact (tensor_product_polynomial_equiv R S).bijective,
end 

open category_theory category_theory.limits

lemma algebra.is_pushout.to_is_pushout (R S R' S' : Type*) [comm_ring R] [comm_ring S] 
  [comm_ring R'] [comm_ring S']
  [algebra R S] [algebra R R'] [algebra S S'] [algebra R' S'] [algebra R S']
  [is_scalar_tower R R' S'] [is_scalar_tower R S S'] [H : algebra.is_pushout R S R' S'] :
  is_pushout (CommRing.of_hom $ algebra_map R S) (CommRing.of_hom $ algebra_map R R')
   (CommRing.of_hom $ algebra_map S S') (CommRing.of_hom $ algebra_map R' S') :=
begin
  refine ⟨⟨_⟩, ⟨pushout_cocone.is_colimit_aux' _ _⟩⟩,
  { ext x, refine (is_scalar_tower.algebra_map_apply R S S' x)
      .symm.trans (is_scalar_tower.algebra_map_apply R R' S' x : _) },
  { intro s, 
    let T := s.X,
    letI : algebra R T := (s.ι.app $ walking_span.zero).to_algebra,
    let f : S →ₐ[R] T :=
      { commutes' := ring_hom.congr_fun (s.ι.naturality walking_span.hom.fst), ..s.inl },
    let g : R' →ₐ[R] T :=
      { commutes' := ring_hom.congr_fun (s.ι.naturality walking_span.hom.snd), ..s.inr },
    refine ⟨(algebra.pushout_desc S' f g $ λ _ _, mul_comm _ _).to_ring_hom, _, _, _⟩,
    { ext, exact algebra.pushout_desc_left S' f g (λ _ _, mul_comm _ _) x },
    { ext, exact algebra.pushout_desc_right S' f g (λ _ _, mul_comm _ _) x },
    { intros m hm₁ hm₂,
      ext x,
      apply H.1.induction_on x,
  { simp only [map_zero] },
  { intro y, exact (ring_hom.congr_fun hm₂ y).trans
      (algebra.pushout_desc_right S' f g (λ _ _, mul_comm _ _) y).symm },
  { intros y y' e, rw [algebra.smul_def, map_mul, map_mul, e],
    congr' 1, exact (ring_hom.congr_fun hm₁ y).trans
      (algebra.pushout_desc_left  S' f g (λ _ _, mul_comm _ _) y).symm },
  { intros s₁ s₂ e₁ e₂, rw [map_add, map_add, e₁, e₂] } } }
end

end 