import morphisms.immersion
import for_mathlib.local_ring
import for_mathlib.ideal

abbreviation ideal.residue_field {R : Type*} [comm_ring R] (I : ideal R) [I.is_prime] :=
local_ring.residue_field (localization.at_prime I)

noncomputable
instance {R R' : Type*} [comm_ring R'] [comm_ring R] [algebra R' R] (I : ideal R) [I.is_prime] :
  algebra R' I.residue_field :=
((local_ring.residue _).comp $ algebra_map R' $ localization.at_prime I).to_algebra

instance {R R' : Type*} [comm_ring R'] [comm_ring R] [algebra R' R] (I : ideal R) [I.is_prime] :
  is_scalar_tower R' (localization.at_prime I) I.residue_field :=
is_scalar_tower.of_algebra_map_eq' rfl

instance ideal.residue_field.is_scalar_tower_of_is_scalar_tower
  {R R' R'' : Type*} [comm_ring R] [comm_ring R'] [comm_ring R''] [algebra R' R]
  [algebra R'' R] [algebra R'' R'] [is_scalar_tower R'' R' R] (I : ideal R) [I.is_prime] :
  is_scalar_tower R'' R' I.residue_field :=
is_scalar_tower.of_algebra_map_eq' $ by simp only [ring_hom.algebra_map_to_algebra,
  ring_hom.comp_assoc, ← is_scalar_tower.algebra_map_eq]

lemma ideal.residue_field_eq_zero_of_mem {R : Type*} [comm_ring R] {I : ideal R} [I.is_prime] 
  {x} : algebra_map R I.residue_field x = 0 ↔ x ∈ I :=
begin
  rw [ring_hom.algebra_map_to_algebra, ring_hom.comp_apply, local_ring.residue,
    ← ideal.quotient.mk_eq_mk, submodule.quotient.mk_eq_zero,
    is_localization.at_prime.to_map_mem_maximal_iff _ I],
end

lemma ideal.ker_residue_field {R : Type*} [comm_ring R] (I : ideal R) [I.is_prime] :
  (algebra_map R I.residue_field).ker = I :=
ideal.ext (λ x, ideal.residue_field_eq_zero_of_mem)

noncomputable
instance ideal.residue_field.quotient_algebra {R : Type*} [comm_ring R] (I : ideal R) [I.is_prime] :
  algebra (R ⧸ I) I.residue_field :=
(ideal.quotient.lift I (algebra_map R I.residue_field)
  (λ x, ideal.residue_field_eq_zero_of_mem.mpr)).to_algebra

instance ideal.residue_field.quotient_tower {R : Type*} [comm_ring R] (I : ideal R) [I.is_prime] :
  is_scalar_tower R (R ⧸ I) I.residue_field :=
is_scalar_tower.of_algebra_map_eq' rfl

instance {R : Type*} [comm_ring R] (I : ideal R) [I.is_prime] :
  is_fraction_ring (R ⧸ I) I.residue_field :=
begin
  constructor,
  { rintro ⟨y, hy⟩,
    obtain ⟨y, rfl⟩ := ideal.quotient.mk_surjective y,
    rwa [subtype.coe_mk, ring_hom.algebra_map_to_algebra, ideal.quotient.lift_mk,
      is_unit_iff_ne_zero, ne.def, ideal.residue_field_eq_zero_of_mem,
      ← @ideal.mk_ker _ _ I, ring_hom.mem_ker, ← ne.def,
      ← mem_non_zero_divisors_iff_ne_zero] },
  { intro y,
    obtain ⟨y, rfl⟩ := ideal.quotient.mk_surjective y,
    obtain ⟨y, s, rfl⟩ := is_localization.mk'_surjective I.prime_compl y,
    refine ⟨⟨ideal.quotient.mk _ y, ideal.quotient.mk _ (s : R), _⟩, _⟩,
    { rw [mem_non_zero_divisors_iff_ne_zero, ne.def, ← ring_hom.mem_ker, ideal.mk_ker], exact s.2 },
    { dsimp only [subtype.coe_mk, ring_hom.algebra_map_to_algebra, ideal.quotient.lift_mk,
        ring_hom.comp_apply, local_ring.residue],
      rw [← map_mul, mul_comm, is_localization.mul_mk'_eq_mk'_of_mul,
        is_localization.mk'_mul_cancel_left] } },
  { intros x y,
    have : ∀ a (b : non_zero_divisors (R ⧸ I)), (a * b : R ⧸ I) = 0 ↔ a = 0,
    { exact λ a b, mul_right_mem_non_zero_divisors_eq_zero_iff b.2 },
    obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := ⟨ideal.quotient.mk_surjective x, ideal.quotient.mk_surjective y⟩,
    simp only [← sub_eq_zero] { single_pass := tt },
    simp_rw [← sub_mul, ← map_sub, this, exists_const],
    exact ideal.residue_field_eq_zero_of_mem.trans (submodule.quotient.mk_eq_zero _).symm }
end

noncomputable
def ideal.residue_field.map {R S : Type*} [comm_ring R] [comm_ring S] (f : R →+* S)
  (J : ideal S) [J.is_prime] :
  (J.comap f).residue_field →+* J.residue_field :=
local_ring.residue_field.map (localization.at_prime.map f J)

lemma ideal.residue_field.mk_surjective {R : Type*} [comm_ring R] {I : ideal R} [I.is_prime] 
  (x : I.residue_field) : ∃ (a b : R) (hb : b ∉ I), x = algebra_map R _ a / algebra_map R _ b :=
begin
  obtain ⟨a, b, hb, rfl⟩ := @is_fraction_ring.div_surjective (R ⧸ I) _ _ _ _ _ _ x,
  obtain ⟨a, rfl⟩ := ideal.quotient.mk_surjective a,
  obtain ⟨b, rfl⟩ := ideal.quotient.mk_surjective b,
  rw [mem_non_zero_divisors_iff_ne_zero, ne.def, ← ring_hom.mem_ker, ideal.quotient.ker_mk] at hb,
  exact ⟨a, b, hb, rfl⟩,
end

lemma alg_equiv.to_ring_equiv_symm' {R A B : Type*} [comm_ring R] [comm_ring A] [comm_ring B]
  [algebra R A] [algebra R B] (f : A ≃ₐ[R] B): (f : A ≃+* B).symm = f.symm := rfl

@[simps] noncomputable
def ideal.residue_field_congr {R S : Type*} [comm_ring R] (I J : ideal R) [I.is_prime] [J.is_prime]
  (h : I = J) :
  I.residue_field ≃+* J.residue_field :=
begin
  haveI : is_localization.at_prime (localization.at_prime J) I :=
    by unfreezingI { subst h, apply_instance },
  refine
  { inv_fun := local_ring.residue_field.map
      ((is_localization.alg_equiv I.prime_compl (localization.at_prime I)
        (localization.at_prime J) : localization.at_prime I ≃+* localization.at_prime J).symm :
          localization.at_prime J →+* localization.at_prime I),
    left_inv := _,
    right_inv := _,
    .. local_ring.residue_field.map
      ((is_localization.alg_equiv I.prime_compl (localization.at_prime I)
        (localization.at_prime J) : localization.at_prime I ≃+* localization.at_prime J) :
        localization.at_prime I →+* localization.at_prime J) },
  all_goals { intro x, 
    obtain ⟨x, rfl⟩ := ideal.quotient.mk_surjective x,
    obtain ⟨x, s, rfl⟩ := is_localization.mk'_surjective I.prime_compl x,
    dsimp only [local_ring.residue_field.map],
    simp only [ring_hom.to_fun_eq_coe, ideal.quotient.lift_mk, ring_hom.coe_comp,
      function.comp_app, ring_equiv.coe_to_ring_hom, alg_equiv.to_ring_equiv_symm',
      alg_equiv.coe_ring_equiv, is_localization.alg_equiv_mk', is_localization.alg_equiv_symm_mk',
      is_localization.alg_equiv_mk'] },
end