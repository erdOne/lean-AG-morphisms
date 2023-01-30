import dimension_theory.order_height
import ring_theory.ideal.minimal_prime
import dimension_theory.min_generator_card
import dimension_theory.noetherian
import algebra.order.pointwise

variables {R : Type*} [comm_ring R] (I : ideal R)

noncomputable
def ideal.prime_height [I.is_prime] : with_top ℕ :=
set.chain_height (set_of ideal.is_prime ∩ set.Iio I)

noncomputable
def ideal.height : with_top ℕ :=
⨅ (J ∈ I.minimal_primes), @@ideal.prime_height _ J (and.left H).1

lemma ideal.height_eq_prime_height [I.is_prime] : I.height = I.prime_height :=
begin
  delta ideal.height ideal.prime_height,
  rw [ideal.minimal_primes_eq_subsingleton_self],
  simp,
end

@[mk_iff]
class ideal.finite_height : Prop :=
(eq_top_or_height_ne_top : I = ⊤ ∨ I.height ≠ ⊤)

lemma ideal.finite_height_iff_lt {I : ideal R} : I.finite_height ↔ I = ⊤ ∨ I.height < ⊤ :=
by { rw ideal.finite_height_iff, congr', simp }

lemma ideal.height_ne_top {I : ideal R} (hI : I ≠ ⊤) [h : I.finite_height] : I.height ≠ ⊤ :=
(h.1 : _).resolve_left hI

lemma ideal.height_lt_top {I : ideal R} (hI : I ≠ ⊤) [h : I.finite_height] : I.height < ⊤ :=
lt_of_le_of_ne le_top (ideal.height_ne_top hI)

lemma ideal.prime_height_ne_top (I : ideal R) [I.finite_height] [h : I.is_prime] :
  I.prime_height ≠ ⊤ :=
I.height_eq_prime_height ▸ (ideal.height_ne_top h.1)

lemma ideal.prime_height_lt_top (I : ideal R) [I.finite_height] [h : I.is_prime] :
  I.prime_height < ⊤ :=
I.height_eq_prime_height ▸ (ideal.height_lt_top h.1)

lemma ideal.prime_height_succ [h : I.is_prime] :
  I.prime_height + 1 = set.chain_height (set_of ideal.is_prime ∩ set.Iic I) :=
begin
  convert (set.chain_height_insert_of_forall_lt _ I _).symm,
  { rw [set.insert_inter_distrib, set.insert_eq_of_mem], { simp }, { exact h } },
  { intros a ha, exact ha.2 }
end

lemma ideal.prime_height_mono {I J : ideal R} [I.is_prime] [J.is_prime] (e : I ≤ J) :
  I.prime_height ≤ J.prime_height :=
set.chain_height_le_of_subset (set.inter_subset_inter set.subset.rfl $ set.Iio_subset_Iio e)

lemma ideal.prime_height_add_one_le_of_lt {I J : ideal R} [I.is_prime] [J.is_prime] (e : I < J) :
  I.prime_height + 1 ≤ J.prime_height :=
I.prime_height_succ.trans_le
  (set.chain_height_le_of_subset (set.inter_subset_inter set.subset.rfl $ set.Iic_subset_Iio.mpr e))

lemma ideal.prime_height_strict_mono {I J : ideal R} [I.is_prime] [J.is_prime]
  (e : I < J) [J.finite_height] :
  I.prime_height < J.prime_height :=
begin
  have H := ideal.prime_height_add_one_le_of_lt e,
  cases hJ : J.prime_height with n,
  { exact (J.prime_height_ne_top hJ).elim },
  cases hI : I.prime_height with m; rw [hI, hJ] at H,
  { rw [with_top.none_eq_top, top_add, ← eq_top_iff] at H, cases H },
  { have : (m : with_top ℕ) + (1 : ℕ) ≤ n := H,
    rw [← with_top.coe_add, with_top.coe_le_coe, nat.add_one_le_iff] at this,
    exact with_top.coe_lt_coe.mpr this },
end

lemma with_top.coe_lt_iff_add_one_le {n : ℕ} {m : ℕ∞} : 
  ↑n < m ↔ ↑n + 1 ≤ m :=
begin
  cases m; simp only [with_top.none_eq_top, with_top.some_eq_coe, ← with_top.coe_one,
    with_top.top_add, ← with_top.coe_add, with_top.coe_le_coe, with_top.coe_lt_coe,
    with_top.nat_ne_top, not_top_lt, top_le_iff, nat.lt_iff_add_one_le, le_top,
    with_top.coe_lt_top],
end

lemma ideal.height_strict_mono_of_is_prime {I J : ideal R} [I.is_prime]
  (e : I < J) [I.finite_height] :
  I.height < J.height :=
begin
  rw [ideal.height_eq_prime_height I, ideal.height,
    ← enat.coe_to_nat_eq_self.mpr (ideal.prime_height_ne_top I),
    with_top.coe_lt_iff_add_one_le, le_infi₂_iff],
  simp_rw [← with_top.coe_lt_iff_add_one_le, enat.coe_to_nat_eq_self.mpr
    (ideal.prime_height_ne_top I)],
  intros K hK,
  haveI := hK.1.1,
  cases hn : K.prime_height with n,
  { rw with_top.none_eq_top, exact ideal.prime_height_lt_top _ },
  haveI : K.finite_height := ⟨or.inr _⟩, 
  { exact hn ▸ ideal.prime_height_strict_mono (e.trans_le hK.1.2) },
  { rw [ideal.height_eq_prime_height, hn], exact with_top.coe_ne_top }
end

lemma ideal.minimal_primes_eq_empty_iff : I.minimal_primes = ∅ ↔ I = ⊤ :=
begin
  split,
  { intros e,
    by_contra h,
    obtain ⟨M, hM, hM'⟩ := ideal.exists_le_maximal I h,
    resetI,
    obtain ⟨p, hp, _⟩ := ideal.exists_minimal_primes_le hM',
    show p ∈ (∅ : set (ideal R)), by rwa ← e },
  { contrapose,
    intros h e,
    rw [← ne.def, set.ne_empty_iff_nonempty] at h,
    obtain ⟨p, hp⟩ := h,
    exact (hp.1.1.1 : _) (eq_top_iff.mpr (e.symm.trans_le hp.1.2)) }
end

lemma ideal.minimal_primes_top : (⊤ : ideal R).minimal_primes = ∅ :=
(ideal.minimal_primes_eq_empty_iff _).mpr rfl

lemma ideal.height_top : ideal.height (⊤ : ideal R) = ⊤ :=
begin
  simp_rw [ideal.height, ideal.prime_height, ideal.minimal_primes_top],
  simp
end

lemma ideal.height_mono {I J : ideal R} (h : I ≤ J) : I.height ≤ J.height :=
begin
  apply le_infi₂ _,
  intros p hp,
  haveI := hp.1.1,
  obtain ⟨q, hq, e⟩ := ideal.exists_minimal_primes_le (h.trans hp.1.2),
  haveI := hq.1.1,
  exact (infi₂_le q hq).trans (ideal.prime_height_mono e)
end

lemma with_top.supr_add {ι : Sort*} [nonempty ι]
  (f : ι → with_top ℕ) (x : with_top ℕ) :
  supr f + x = ⨆ i, f i + x :=
begin
  cases x, { simp_rw [with_top.none_eq_top, add_top, supr_const] },
  have : ↑x ≤ ⨆ i, f i + ↑x,
  { refine le_trans _ (le_supr _ $ classical.arbitrary _), exact le_add_left rfl.le },
  rw with_top.some_eq_coe,
  apply le_antisymm,
  { rw [← tsub_add_cancel_of_le this],
    refine add_le_add (supr_le $ λ i, _) rfl.le,
    apply (with_top.add_le_add_iff_right (with_top.coe_ne_top : (x : with_top ℕ) ≠ ⊤)).mp,
    rw [tsub_add_cancel_of_le this],
    exact le_supr _ i },
  { exact supr_le (λ i, add_le_add (le_supr f i) rfl.le) }
end

lemma with_top.supr₂_add {ι : Sort*} {p : ι → Sort*} (hs : Exists p)
  (f : ∀ (i : ι), p i → with_top ℕ) (x : with_top ℕ) :
  (⨆ (i : ι) (h : p i), f i h) + x = ⨆ (i : ι) (h : p i), f i h + x :=
begin
  haveI : nonempty { i // p i } := ⟨⟨_, hs.some_spec⟩⟩,
  rw [supr_subtype', supr_subtype', with_top.supr_add]
end

noncomputable
def krull_dimension (R : Type*) [comm_ring R] : with_top ℕ :=
⨆ (I : ideal R) [I.is_prime], by exactI I.prime_height

@[mk_iff]
class finite_krull_dimensional (R : Type*) [comm_ring R] : Prop :=
(krull_dimension_ne_top : krull_dimension R ≠ ⊤)

lemma krull_dimension_ne_top (R : Type*) [comm_ring R] [h : finite_krull_dimensional R] :
  krull_dimension R ≠ ⊤ :=
h.1

lemma krull_dimension_lt_top (R : Type*) [comm_ring R] [finite_krull_dimensional R] :
  krull_dimension R < ⊤ :=
lt_of_le_of_ne le_top (krull_dimension_ne_top R)

lemma finite_krull_dimensional_iff_lt :
  finite_krull_dimensional R ↔ krull_dimension R < ⊤ :=
by simp [finite_krull_dimensional_iff]

lemma krull_dimension_of_subsingleton (R : Type*) [comm_ring R] [subsingleton R] :
  krull_dimension R = 0 :=
begin
  apply supr₂_eq_bot.mpr,
  intros i hI,
  exact ((hI.1 : _) (subsingleton.elim _ _)).elim
end

@[priority 100]
instance finite_krull_dimensional_of_subsingleton [subsingleton R] : finite_krull_dimensional R :=
by { rw [finite_krull_dimensional_iff, krull_dimension_of_subsingleton], rintro ⟨⟩ }

lemma ideal.prime_height_le_krull_dimension [I.is_prime] : I.prime_height ≤ krull_dimension R :=
le_supr₂ _ _

@[priority 900]
instance ideal.finite_height_of_finite_dimensional [finite_krull_dimensional R] :
  I.finite_height :=
begin
  rw [ideal.finite_height_iff_lt, or_iff_not_imp_left],
  intro e,
  obtain ⟨M, hM, hM'⟩ := ideal.exists_le_maximal I e,
  refine (ideal.height_mono hM').trans_lt (has_le.le.trans_lt _ (krull_dimension_lt_top R)),
  resetI,
  rw ideal.height_eq_prime_height,
  exact M.prime_height_le_krull_dimension
end

lemma krull_dimension_succ (R : Type*) [comm_ring R] [nontrivial R] :
  krull_dimension R + 1 = set.chain_height (set_of ideal.is_prime : set (ideal R)) :=
begin
  have : ∃ I : ideal R, I.is_prime := ⟨_, (ideal.exists_maximal R).some_spec.is_prime⟩,
  rw [krull_dimension, with_top.supr₂_add this, set.chain_height_eq_supr_Iic],
  simpa only [ideal.prime_height_succ]
end

variables {I}

lemma ideal.finite_height_of_le {I J : ideal R} (e : I ≤ J) (hJ : J ≠ ⊤) [J.finite_height] :
  I.finite_height :=
⟨or.inr $ by { rw ← lt_top_iff_ne_top,
  exact (ideal.height_mono e).trans_lt (ideal.height_lt_top hJ) }⟩

lemma ideal.mem_minimal_primes_of_height_eq {I J : ideal R} (e : I ≤ J) [J.is_prime]
  [hJ : J.finite_height]
  (e' : J.height ≤ I.height) : J ∈ I.minimal_primes :=
begin
  obtain ⟨p, h₁, h₂⟩ := ideal.exists_minimal_primes_le e,
  convert h₁,
  refine (eq_of_le_of_not_lt h₂ _).symm,
  intro h₃,
  haveI := h₁.1.1,
  haveI := ideal.finite_height_of_le h₂ ‹J.is_prime›.ne_top,
  exact lt_irrefl _
    ((ideal.height_strict_mono_of_is_prime h₃).trans_le (e'.trans $ ideal.height_mono h₁.1.2))
end

lemma ideal.prime_height_eq_zero_iff [I.is_prime] : I.prime_height = 0 ↔ I ∈ minimal_primes R :=
begin
  rw [ideal.prime_height, set.chain_height_eq_zero_iff],
  split,
  { intro e,
    refine ⟨⟨infer_instance, bot_le⟩, λ J hJ e', (eq_of_le_of_not_lt e' _).symm.le⟩,
    intro e'',
    show J ∈ (∅ : set (ideal R)),
    rw ← e,
    exact ⟨hJ.1, e''⟩ },
  { intro hI,
    ext J,
    suffices : J.is_prime → ¬J < I, { simpa },
    intros hJ e,
    exact not_le_of_lt e (hI.2 ⟨hJ, bot_le⟩ e.le) }
end

lemma ideal.is_maximal_of_prime_height_eq_krull_dimesion
  [h : I.is_prime] [finite_krull_dimensional R]
  (e : I.prime_height = krull_dimension R) : I.is_maximal :=
begin
  casesI subsingleton_or_nontrivial R,
  { exact ((h.1 : _) $ subsingleton.elim _ _).elim },
  have := congr_arg (λ x : with_top ℕ, x + 1) e,
  dsimp at this,
  rw [ideal.prime_height_succ] at this,
  refine ⟨⟨h.1, _⟩⟩,
  intros J hJ,
  by_contra e',
  obtain ⟨M, hM, hM'⟩ := ideal.exists_le_maximal J e',
  have H : (insert M (set_of ideal.is_prime ∩ set.Iic I)).chain_height =
    krull_dimension R + 1 + 1,
  { rw [← this, set.chain_height_insert_of_forall_lt],
    intros I' hI',
    calc I' ≤ I : hI'.2
        ... < J : hJ
        ... ≤ M : hM' },
  have : krull_dimension R + 1 + 1 ≤ set.chain_height (set_of ideal.is_prime),
  { rw ← H, apply set.chain_height_le_of_subset, rintros K (rfl|⟨h, _⟩), exacts [hM.is_prime, h] },
  cases h : krull_dimension R with x,
  { exact krull_dimension_ne_top R h },
  { rw [← krull_dimension_succ, h] at this, linarith [with_top.coe_le_coe.mp this] }
end

lemma local_ring.maximal_ideal_prime_height [local_ring R] :
  (local_ring.maximal_ideal R).prime_height = krull_dimension R :=
begin
  apply le_antisymm,
  { apply ideal.prime_height_le_krull_dimension },
  { apply supr₂_le _,
    introsI I hI,
    apply ideal.prime_height_mono,
    exact local_ring.le_maximal_ideal hI.1 }
end

lemma local_ring.maximal_ideal_height [local_ring R] :
  (local_ring.maximal_ideal R).height = krull_dimension R :=
by rw [ideal.height_eq_prime_height, local_ring.maximal_ideal_prime_height]

lemma ideal.prime_height_eq_krull_dimesion_iff [local_ring R] [I.is_prime]
  [finite_krull_dimensional R] :
  I.prime_height = krull_dimension R ↔ I = local_ring.maximal_ideal R :=
begin
  split,
  { exact λ e, local_ring.eq_maximal_ideal (ideal.is_maximal_of_prime_height_eq_krull_dimesion e) },
  { unfreezingI { rintro rfl }, rw local_ring.maximal_ideal_prime_height }
end

lemma set.chain_height_univ {α : Type*} [preorder α] (s : set α) : 
  (set.univ : set s).chain_height = s.chain_height :=
begin
  conv_rhs { rw [← @subtype.range_coe _ s, ← set.image_univ] },
  rw set.chain_height_image,
  intros x y, refl,
end

lemma order_iso.chain_height_eq {α β : Type*} [preorder α] [preorder β]
  (e : α ≃o β) : (set.univ : set α).chain_height = (set.univ : set β).chain_height :=
begin
  rw [← set.range_iff_surjective.mpr e.surjective, ← set.image_univ, set.chain_height_image],
  exact λ _ _, e.lt_iff_lt.symm
end

lemma with_top.add_injective {n : ℕ∞} (hn : n ≠ ⊤) : function.injective (λ a, a + n) :=
λ a b e, ((with_top.add_le_add_iff_right hn).mp e.le).antisymm
    ((with_top.add_le_add_iff_right hn).mp e.ge) 

lemma is_localization.prime_height (S : submonoid R)
  (A : Type*) [comm_ring A] [algebra R A] [is_localization S A]
  (J : ideal A) (hJ : J.is_prime) : 
  J.prime_height = (J.comap (algebra_map R A)).prime_height :=
begin
  apply with_top.add_injective with_top.one_ne_top,
  dsimp only,
  rw [ideal.prime_height_succ, ideal.prime_height_succ, ← set.chain_height_univ,
    ← set.chain_height_univ (_ ∩ _)],
  let e := is_localization.order_iso_of_prime S A,
  have H : ∀ p : ideal R, p ≤ J.comap (algebra_map R A) → disjoint (S : set R) p,
  { exact λ p hp, set.disjoint_of_subset_right hp (e ⟨_, ‹J.is_prime›⟩).2.2 },
  refine order_iso.chain_height_eq
  { to_fun := λ I, ⟨I.1.comap (algebra_map R A), (e ⟨_, I.2.1⟩).2.1, ideal.comap_mono I.2.2⟩,
    inv_fun := λ I, ⟨_, (e.symm ⟨_, I.2.1, H _ I.2.2⟩).2, ideal.map_le_iff_le_comap.mpr I.2.2⟩,
    left_inv := λ I, subtype.ext (by injection (e.left_inv ⟨_, I.2.1⟩)),
    right_inv := λ I, subtype.ext (by injection (e.right_inv ⟨_, I.2.1, H _ I.2.2⟩)),
    map_rel_iff' := λ I₁ I₂, @rel_iso.map_rel_iff _ _ _ _ e ⟨_, I₁.2.1⟩ ⟨_, I₂.2.1⟩ }
end

lemma ideal.minimal_primes_comap_subset {A : Type*} [comm_ring A] (f : R →+* A) (J : ideal A) : 
  (J.comap f).minimal_primes ⊆ ideal.comap f '' J.minimal_primes :=
λ p hp, let h := ideal.exists_minimal_primes_comap_eq f p hp in
  ⟨h.some, h.some_spec.some, h.some_spec.some_spec⟩

lemma is_localization.minimal_primes_comap (S : submonoid R) (A : Type*) [comm_ring A]
  [algebra R A] [is_localization S A] (J : ideal A) : 
  (J.comap (algebra_map R A)).minimal_primes = ideal.comap (algebra_map R A) '' J.minimal_primes :=
begin
  rcases eq_or_ne J ⊤ with (rfl|hJ),
  { simp_rw [ideal.comap_top, ideal.minimal_primes_top, set.image_empty] },
  refine (ideal.minimal_primes_comap_subset _ _).antisymm _,
  rintro _ ⟨p, hp, rfl⟩,
  let i := is_localization.order_iso_of_prime S A,
  refine ⟨⟨@@ideal.is_prime.comap _ _ _ _ hp.1.1, ideal.comap_mono hp.1.2⟩, λ q hq e, _⟩,
  obtain ⟨⟨q', h₁⟩, h₂⟩ := i.surjective ⟨q, hq.1, set.disjoint_of_subset_right e (i ⟨_, hp.1.1⟩).2.2⟩,
  replace h₂ : q'.comap (algebra_map R A) = q := by injection h₂, subst h₂,
  replace e := @ideal.map_mono _ _ _ _ _ _ (algebra_map R A) _ _ e,
  replace hq := @ideal.map_mono _ _ _ _ _ _ (algebra_map R A) _ _ hq.2,
  simp_rw [is_localization.map_comap S A] at e hq,
  exact ideal.comap_mono (hp.2 ⟨h₁, hq⟩ e)
end

lemma is_localization.disjoint_comap_iff (S : submonoid R) (A : Type*) [comm_ring A]
  [algebra R A] [is_localization S A] (J : ideal A) : 
  disjoint (S : set R) (J.comap $ algebra_map R A) ↔ J ≠ ⊤ :=
begin
  rw ← iff_not_comm, split,
  { rintro rfl, rw ideal.comap_top, apply set.disjoint_univ.not.mpr _,
    rw [← ne.def, set.ne_empty_iff_nonempty], exact ⟨_, S.one_mem⟩ },
  { rw [disjoint_iff, set.bot_eq_empty, ← ne.def, set.ne_empty_iff_nonempty],
    rintro ⟨x, hx, hx' : algebra_map R A x ∈ J⟩,
    exact J.eq_top_of_is_unit_mem hx' (is_localization.map_units A ⟨x, hx⟩) }
end

lemma is_localization.minimal_primes_map (S : submonoid R) (A : Type*) [comm_ring A]
  [algebra R A] [is_localization S A] (J : ideal R) : 
  (J.map (algebra_map R A)).minimal_primes =
    ideal.comap (algebra_map R A) ⁻¹' J.minimal_primes :=
begin
  ext p, split,
  { intro hp,
    refine ⟨⟨@@ideal.is_prime.comap _ _ _ _ hp.1.1, ideal.map_le_iff_le_comap.mp hp.1.2⟩, _⟩,
    rintros I hI e, 
    have hI' : disjoint (S : set R) I := (set.disjoint_of_subset_right e $
      ((is_localization.is_prime_iff_is_prime_disjoint S A _).mp hp.1.1).2),
    refine (ideal.comap_mono $
      hp.2 ⟨_, ideal.map_mono hI.2⟩ (ideal.map_le_iff_le_comap.mpr e)).trans_eq _,
    { exact is_localization.is_prime_of_is_prime_disjoint S A I hI.1 hI' },
    { exact is_localization.comap_map_of_is_prime_disjoint S A _ hI.1 hI' } },
  { intro hp,
    refine ⟨⟨_, ideal.map_le_iff_le_comap.mpr hp.1.2⟩, _⟩,
    { rw [is_localization.is_prime_iff_is_prime_disjoint S A,
        is_localization.disjoint_comap_iff S A],
      refine ⟨hp.1.1, _⟩, rintro rfl, exact hp.1.1.ne_top rfl },
    { intros I hI e,
      rw [← is_localization.map_comap S A I, ← is_localization.map_comap S A p],
      exact ideal.map_mono (hp.2 ⟨@@ideal.is_prime.comap _ _ _ _ hI.1,
        ideal.map_le_iff_le_comap.mp hI.2⟩ (ideal.comap_mono e)) } }
end

lemma is_localization.height (S : submonoid R)
  (A : Type*) [comm_ring A] [nontrivial A] [algebra R A] [is_localization S A]
  (J : ideal A) : 
  J.height = (J.comap (algebra_map R A)).height :=
begin
  delta ideal.height,
  simp_rw [is_localization.prime_height S A, is_localization.minimal_primes_comap S A,
    ← ideal.height_eq_prime_height, infi_image]
end

lemma is_localization.at_prime.comap_maximal_ideal {R : Type*} (S : Type*) [comm_ring R] [comm_ring S]
  (I : ideal R) [I.is_prime] [algebra R S] [is_localization.at_prime S I] [local_ring S] :
  (local_ring.maximal_ideal S).comap (algebra_map R S) = I :=
ideal.ext $ λ x, by
simpa only [ideal.mem_comap] using is_localization.at_prime.to_map_mem_maximal_iff _ I x

lemma is_localization.at_prime.krull_dimension_eq_height (I : ideal R) [I.is_prime]
  (A : Type*) [comm_ring A] [nontrivial A] [algebra R A] [is_localization.at_prime A I] : 
  krull_dimension A = I.height :=
begin
  haveI := is_localization.at_prime.local_ring A I,
  rw [← local_ring.maximal_ideal_prime_height,
    is_localization.prime_height I.prime_compl A,
    ← is_localization.at_prime.comap_maximal_ideal A I,
    ideal.height_eq_prime_height],
end

lemma submodule.spanrank_eq_zero_iff : I.spanrank = 0 ↔ I = ⊥ :=
begin
  split,
  { intro e,
    have H : submodule.fg I,
    { rw [← submodule.spanrank_ne_top_iff, e], rintro ⟨⟩ },
    rw [H.spanrank_eq, ← with_top.coe_zero, with_top.coe_eq_coe] at e,
    have := H.exists_generator_eq_min_generator_card,
    rw e at this,
    obtain ⟨f, hf⟩ := this,
    rwa [show set.range f = ∅, by simp, submodule.span_empty, eq_comm] at hf },
  { rintro rfl,
    rw [← bot_eq_zero, eq_bot_iff, bot_eq_zero, bot_eq_zero, ← with_top.coe_zero,
      submodule.fg.min_generator_card_le_iff_exists],
    have f : fin 0 → R := λ _, 0,
    refine ⟨f, by rw [show set.range f = ∅, by simp, submodule.span_empty, bot_eq_zero]⟩ }
end

lemma submodule.spanrank_sup {p q : ideal R} :
  (p ⊔ q).spanrank ≤ p.spanrank + q.spanrank :=
begin
  by_cases hp : submodule.fg p,
  swap,
  { rw [← submodule.spanrank_ne_top_iff, not_ne_iff] at hp,
    rw [hp, top_add], exact le_top },
  by_cases hq : submodule.fg q,
  swap,
  { rw [← submodule.spanrank_ne_top_iff, not_ne_iff] at hq,
    rw [hq, add_top], exact le_top },
  obtain ⟨f, hf⟩ := hp.exists_generator_eq_min_generator_card,
  obtain ⟨g, hg⟩ := hq.exists_generator_eq_min_generator_card,
  rw submodule.fg_iff_spanrank_eq at hp hq,
  rw [hp, hq, ← with_top.coe_add, submodule.fg.min_generator_card_le_iff_exists],
  refine ⟨(sum.elim f g) ∘ fin_sum_fin_equiv.symm, _⟩,
  rw [set.range_comp, set.range_iff_surjective.mpr (equiv.surjective _), set.image_univ,
    set.sum.elim_range, submodule.span_union, hf, hg],
end

lemma submodule.spanrank_span_set_finite {s : set R} (hs : s.finite) :
  (submodule.span R s).spanrank ≤ hs.to_finset.card :=
begin
  rw submodule.fg.min_generator_card_le_iff_exists,
  refine ⟨subtype.val ∘ hs.to_finset.equiv_fin.symm, _⟩,
  rw [set.range_comp, set.range_iff_surjective.mpr (equiv.surjective _), set.image_univ,
    subtype.range_val],
  congr, ext, exact hs.mem_to_finset,
end

lemma submodule.spanrank_bot : (⊥ : ideal R).spanrank = 0 :=
submodule.spanrank_eq_zero_iff.mpr rfl

lemma mem_minimal_primes_of_height_eq {I J : ideal R} [J.is_prime] (e : I ≤ J)
  (e' : I.height = J.prime_height) [J.finite_height] : J ∈ I.minimal_primes :=
begin
  refine ⟨⟨infer_instance, e⟩, λ K hK e'', (eq_of_le_of_not_lt e'' _).symm.le⟩,
  intro e''',
  haveI := hK.1,
  rw ← lt_self_iff_false J.prime_height,
  calc J.prime_height = I.height       : e'.symm
                  ... ≤ K.height       : ideal.height_mono hK.2
                  ... = K.prime_height : K.height_eq_prime_height
                  ... < J.prime_height : ideal.prime_height_strict_mono e'''
end

lemma exists_spanrank_le_and_le_height_of_le_height [is_noetherian_ring R] (I : ideal R) (r : ℕ)
  (hr : ↑r ≤ I.height) :
  ∃ J ≤ I, J.spanrank ≤ r ∧ ↑r ≤ J.height :=
begin
  induction r with r H,
  { refine ⟨⊥, bot_le, _, zero_le _⟩, rw submodule.spanrank_bot, exact rfl.le },
  { obtain ⟨J, h₁, h₂, h₃⟩ := H ((with_top.coe_le_coe.mpr r.le_succ).trans hr),
    let S := { K | K ∈ J.minimal_primes ∧ ideal.height K = r },
    have hS : S.finite := set.finite.subset J.minimal_primes_finite (λ _ h, h.1),
    have : ¬ ↑I ⊆ ⋃ J ∈ hS.to_finset, (J : set R),
    { refine (ideal.subset_union_prime ⊥ ⊥ _).not.mpr _,
      { rintro K hK - -, rw set.finite.mem_to_finset at hK, exact hK.1.1.1 },
      { push_neg,
        intros K hK e,
        have := hr.trans (ideal.height_mono e),
        rw set.finite.mem_to_finset at hK,
        rw [hK.2, with_top.coe_le_coe, ← not_lt] at this,
        exact this r.lt_succ_self } },
    simp_rw [set.not_subset, set.mem_Union, not_exists, set.finite.mem_to_finset] at this,
    obtain ⟨x, hx₁, hx₂⟩ := this,
    refine ⟨J ⊔ ideal.span {x}, sup_le h₁ _, _, _⟩,
    { rwa [ideal.span_le, set.singleton_subset_iff] },
    { refine submodule.spanrank_sup.trans _,
      rw [nat.succ_eq_add_one, with_top.coe_add],
      refine add_le_add h₂ _,
      refine (submodule.spanrank_span_set_finite $ set.to_finite _).trans _,
      simp },
    { refine le_infi₂ _,
      intros p hp,
      haveI := hp.1.1,
      by_cases p.height = ⊤,
      { rw [← p.height_eq_prime_height, h], exact le_top },
      haveI : p.finite_height := ⟨or.inr h⟩,
      have := ideal.height_mono (le_sup_left.trans hp.1.2),
      suffices h : ↑r ≠ p.prime_height,
      { rw [nat.succ_eq_add_one, with_top.coe_add],
        have := h₃.trans this,
        rw ideal.height_eq_prime_height at this,
        exact enat.add_one_le_of_lt (lt_of_le_of_ne this h) },
      intro e,
      apply hx₂ p,
      { have : J.height = p.prime_height,
        { apply le_antisymm, { rwa ← p.height_eq_prime_height }, { rwa ← e } },
        refine ⟨mem_minimal_primes_of_height_eq (le_sup_left.trans hp.1.2) this, _⟩,
        rwa [p.height_eq_prime_height, eq_comm] },
      { apply hp.1.2,
        apply ideal.mem_sup_right,
        apply ideal.subset_span,
        exact set.mem_singleton _ } } }
end
