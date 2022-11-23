import order.upper_lower
import topology.inseparable

/-! ### Upper/lower sets and fibrations -/

open order_dual set

variables {α β γ : Type*} {ι : Sort*} {κ : ι → Sort*}

namespace relation

variables {f : α → β} {s : set α}

lemma fibration.is_lower_set_image [has_le α] [has_le β] (hf : fibration (≤) (≤) f)
  {s : set α} (hs : is_lower_set s) : is_lower_set (f '' s) :=
by { rintros _ y' e ⟨x, hx, rfl⟩, obtain ⟨y, e', rfl⟩ := hf e, exact ⟨_, hs e' hx, rfl⟩ }

alias fibration.is_lower_set_image ← _root_.is_lower_set.image_fibration

lemma fibration_iff_is_lower_set_image_Iic [preorder α] [has_le β] :
  fibration (≤) (≤) f ↔ ∀ x, is_lower_set (f '' Iic x) :=
⟨λ h x, (is_lower_set_Iic x).image_fibration h, λ H x y' e, H x e ⟨x, le_rfl, rfl⟩⟩

lemma fibration_iff_is_lower_set_image [preorder α] [has_le β] :
  fibration (≤) (≤) f ↔ ∀ s, is_lower_set s → is_lower_set (f '' s) :=
⟨fibration.is_lower_set_image,
  λ H, fibration_iff_is_lower_set_image_Iic.mpr (λ x, H _ $ is_lower_set_Iic x)⟩

lemma fibration_iff_image_Iic [preorder α] [preorder β] (hf : monotone f) :
  fibration (≤) (≤) f ↔ ∀ x, f '' Iic x = Iic (f x) :=
⟨λ H x, le_antisymm (λ _ ⟨y, hy, e⟩, e ▸ hf hy)
  ((H.is_lower_set_image (is_lower_set_Iic x)).Iic_subset ⟨x, le_rfl, rfl⟩),
  λ H, fibration_iff_is_lower_set_image_Iic.mpr (λ x, (H x).symm ▸ is_lower_set_Iic (f x))⟩

lemma fibration.is_upper_set_image [has_le α] [has_le β] (hf : fibration (≥) (≥) f)
  {s : set α} (hs : is_upper_set s) : is_upper_set (f '' s) :=
@fibration.is_lower_set_image αᵒᵈ βᵒᵈ _ _ _ hf s hs

alias fibration.is_upper_set_image ← _root_.is_upper_set.image_fibration

lemma fibration_iff_is_upper_set_image_Ici [preorder α] [has_le β] :
  fibration (≥) (≥) f ↔ ∀ x, is_upper_set (f '' Ici x) :=
@fibration_iff_is_lower_set_image_Iic αᵒᵈ βᵒᵈ _ _ _

lemma fibration_iff_is_upper_set_image [preorder α] [has_le β] :
  fibration (≥) (≥) f ↔ ∀ s, is_upper_set s → is_upper_set (f '' s) :=
@fibration_iff_is_lower_set_image αᵒᵈ βᵒᵈ _ _ _

lemma fibration_iff_image_Ici [preorder α] [preorder β] (hf : monotone f) :
  fibration (≥) (≥) f ↔ ∀ x, f '' Ici x = Ici (f x) :=
fibration_iff_image_Iic hf.dual

end relation

section

variable [preorder α]
variables {f : α → β} {s : set α}

@[norm_cast] lemma coe_upper_closure' (s : set α) : ↑(upper_closure s) = ⋃ a ∈ s, set.Ici a :=
by { ext, simp }

@[norm_cast] lemma coe_lower_closure' (s : set α) : ↑(lower_closure s) = ⋃ a ∈ s, set.Iic a :=
by { ext, simp }

@[simp] lemma upper_closure_eq :
  ↑(upper_closure s) = s ↔ is_upper_set s :=
⟨λ h, h ▸ upper_set.upper _, is_upper_set.upper_closure⟩

@[simp] lemma lower_closure_eq :
  ↑(lower_closure s) = s ↔ is_lower_set s :=
@upper_closure_eq αᵒᵈ _ _

end

local attribute [instance] specialization_preorder


open set filter function
open_locale topological_space filter
variables {X Y Z : Type*} {π : ι → Type*} [topological_space X] [topological_space Y]
  [topological_space Z] [∀ i, topological_space (π i)] {x y z : X} {s : set X} {f : X → Y}


lemma closure_singleton_eq_Iic (x : X) : closure {x} = Iic x :=
ext $ λ _, specializes_iff_mem_closure.symm

/-- A subset `S` of a topological space is stable under specialization
if `x ∈ S → y ∈ S` for all `x ⤳ y`. -/
def stable_under_specialization (s : set X) : Prop :=
∀ ⦃x y⦄, x ⤳ y → x ∈ s → y ∈ s

/-- A subset `S` of a topological space is stable under specialization
if `x ∈ S → y ∈ S` for all `y ⤳ x`. -/
def stable_under_generalization (s : set X) : Prop :=
∀ ⦃x y⦄, y ⤳ x → x ∈ s → y ∈ s

example {s : set X} : stable_under_specialization s ↔ is_lower_set s := iff.rfl
example {s : set X} : stable_under_generalization s ↔ is_upper_set s := iff.rfl

lemma is_closed.stable_under_specialization {s : set X} (hs : is_closed s) :
  stable_under_specialization s :=
λ x y e, e.mem_closed hs

lemma is_open.stable_under_generalization {s : set X} (hs : is_open s) :
  stable_under_generalization s :=
λ x y e, e.mem_open hs

@[simp]
lemma stable_under_specialization_compl_iff {s : set X} :
  stable_under_specialization sᶜ ↔ stable_under_generalization s :=
is_lower_set_compl

@[simp]
lemma stable_under_generalization_compl_iff {s : set X} :
  stable_under_generalization sᶜ ↔ stable_under_specialization s :=
is_upper_set_compl

alias stable_under_specialization_compl_iff ↔ _ stable_under_generalization.compl
alias stable_under_generalization_compl_iff ↔ _ stable_under_specialization.compl

lemma stable_under_specialization_sUnion (S : set (set X))
  (H : ∀ s ∈ S, stable_under_specialization s) : stable_under_specialization (⋃₀ S) :=
is_lower_set_sUnion H

lemma stable_under_specialization_sInter (S : set (set X))
  (H : ∀ s ∈ S, stable_under_specialization s) : stable_under_specialization (⋂₀ S) :=
is_lower_set_sInter H

lemma stable_under_generalization_sUnion (S : set (set X))
  (H : ∀ s ∈ S, stable_under_generalization s) : stable_under_generalization (⋃₀ S) :=
is_upper_set_sUnion H

lemma stable_under_generalization_sInter (S : set (set X))
  (H : ∀ s ∈ S, stable_under_generalization s) : stable_under_generalization (⋂₀ S) :=
is_upper_set_sInter H

lemma stable_under_specialization_Union {ι : Sort*} (S : ι → set X)
  (H : ∀ i, stable_under_specialization (S i)) : stable_under_specialization (⋃ i, S i) :=
is_lower_set_Union H

lemma stable_under_specialization_Inter {ι : Sort*} (S : ι → set X)
  (H : ∀ i, stable_under_specialization (S i)) : stable_under_specialization (⋂ i, S i) :=
is_lower_set_Inter H

lemma stable_under_generalization_Union {ι : Sort*} (S : ι → set X)
  (H : ∀ i, stable_under_generalization (S i)) : stable_under_generalization (⋃ i, S i) :=
is_upper_set_Union H

lemma stable_under_generalization_Inter {ι : Sort*} (S : ι → set X)
  (H : ∀ i, stable_under_generalization (S i)) : stable_under_generalization (⋂ i, S i) :=
is_upper_set_Inter H

lemma Union_closure_singleton_eq_iff {s : set X} :
  (⋃ x ∈ s, closure {x}) = s ↔ stable_under_specialization s :=
show _ ↔ is_lower_set s,
  by simp only [closure_singleton_eq_Iic, ← lower_closure_eq, coe_lower_closure']

lemma stable_under_specialization_iff_eq_Union {s : set X} :
  stable_under_specialization s ↔ (⋃ x ∈ s, closure {x}) = s :=
Union_closure_singleton_eq_iff.symm

alias stable_under_specialization_iff_eq_Union ↔ stable_under_specialization.Union_eq _

/-- A set is stable under specialization iff it is a union of closed sets. -/
lemma stable_under_specialization_iff_exists_sUnion_eq {s : set X} :
  stable_under_specialization s ↔ ∃ (S : set (set X)), (∀ s ∈ S, is_closed s) ∧ ⋃₀ S = s :=
begin
  refine ⟨λ H, ⟨(λ x : X, closure {x}) '' s, _, _⟩, λ ⟨S, hS, e⟩, e ▸
    stable_under_specialization_sUnion S (λ x hx, (hS x hx).stable_under_specialization)⟩,
  { rintros _ ⟨_, _, rfl⟩, exact is_closed_closure },
  { conv_rhs { rw ← H.Union_eq }, simp }
end

/-- A set is stable under generalization iff it is an intersection of open sets. -/
lemma stable_under_generalization_iff_exists_sInter_eq {s : set X} :
  stable_under_generalization s ↔ ∃ (S : set (set X)), (∀ s ∈ S, is_open s) ∧ ⋂₀ S = s :=
begin
  refine ⟨_, λ ⟨S, hS, e⟩, e ▸
    stable_under_generalization_sInter S (λ x hx, (hS x hx).stable_under_generalization)⟩,
  rw [← stable_under_specialization_compl_iff, stable_under_specialization_iff_exists_sUnion_eq],
  exact λ ⟨S, h₁, h₂⟩, ⟨has_compl.compl '' S, λ s ⟨t, ht, e⟩, e ▸ (h₁ t ht).is_open_compl,
    compl_injective ((sUnion_eq_compl_sInter_compl S).symm.trans h₂)⟩
end

lemma stable_under_specialization.preimage {s : set Y}
  (hs : stable_under_specialization s) (hf : continuous f) :
  stable_under_specialization (f ⁻¹' s) :=
is_lower_set.preimage hs hf.specialization_monotone

lemma stable_under_generalization.preimage {s : set Y}
  (hs : stable_under_generalization s) (hf : continuous f) :
  stable_under_generalization (f ⁻¹' s) :=
is_upper_set.preimage hs hf.specialization_monotone

/-- A map `f` between topological spaces is specializing if specializations lifts along `f`,
i.e. for each `f x' ⤳ y` there is some `x` with `x' ⤳ x` whose image is `y`. -/
def specializing_map (f : X → Y) : Prop :=
relation.fibration (flip (⤳)) (flip (⤳)) f

/-- A map `f` between topological spaces is generalizing if generalizations lifts along `f`,
i.e. for each `y ⤳ f x'` there is some `x ⤳ x'` whose image is `y`. -/
def generalizing_map (f : X → Y) : Prop :=
relation.fibration (⤳) (⤳) f

lemma specializing_map_iff_closure_singleton_subset :
  specializing_map f ↔ ∀ x, closure {f x} ⊆ f '' closure {x} :=
by simpa only [specializing_map, relation.fibration, flip, specializes_iff_mem_closure]

alias specializing_map_iff_closure_singleton_subset ↔ specializing_map.closure_singleton_subset _

lemma specializing_map.stable_under_specialization_image (hf : specializing_map f)
  {s : set X} (hs : stable_under_specialization s) : stable_under_specialization (f '' s) :=
is_lower_set.image_fibration hf hs

alias specializing_map.stable_under_specialization_image ← stable_under_specialization.image

lemma specializing_map_iff_image_singleton_stable_under_specialization :
  specializing_map f ↔ ∀ x, stable_under_specialization (f '' closure {x}) :=
by simpa only [closure_singleton_eq_Iic] using relation.fibration_iff_is_lower_set_image_Iic

lemma specializing_map_iff_stable_under_specialization_image :
  specializing_map f ↔ ∀ s, stable_under_specialization s → stable_under_specialization (f '' s) :=
relation.fibration_iff_is_lower_set_image

lemma specializing_map_iff_closure_singleton (hf : continuous f) :
  specializing_map f ↔ ∀ x, f '' closure {x} = closure {f x} :=
by simpa only [closure_singleton_eq_Iic] using
  relation.fibration_iff_image_Iic hf.specialization_monotone

lemma specializing_map_iff_is_closed_image_closure_singleton (hf : continuous f) :
  specializing_map f ↔ ∀ x, is_closed (f '' closure {x}) :=
begin
  refine ⟨λ h x, _, λ h, specializing_map_iff_image_singleton_stable_under_specialization.mpr
    (λ x, (h x).stable_under_specialization)⟩,
  rw (specializing_map_iff_closure_singleton hf).mp h x,
  exact is_closed_closure
end

lemma is_closed_map.specializing_map (hf : is_closed_map f) : specializing_map f :=
specializing_map_iff_image_singleton_stable_under_specialization.mpr $
  λ x, (hf _ is_closed_closure).stable_under_specialization

lemma inducing.specializing_map (hf : inducing f) (h : stable_under_specialization (range f)) :
  specializing_map f :=
by { intros x y e, obtain ⟨y, rfl⟩ := h e ⟨x, rfl⟩, exact ⟨_, hf.specializes_iff.mp e, rfl⟩ }

lemma inducing.generalizing_map (hf : inducing f) (h : stable_under_generalization (range f)) :
  generalizing_map f :=
by { intros x y e, obtain ⟨y, rfl⟩ := h e ⟨x, rfl⟩, exact ⟨_, hf.specializes_iff.mp e, rfl⟩ }

lemma open_embedding.generalizing_map (hf : open_embedding f) : generalizing_map f :=
hf.to_inducing.generalizing_map hf.open_range.stable_under_generalization

lemma specializing_map.stable_under_specialization_range (h : specializing_map f) :
  stable_under_specialization (range f) :=
@image_univ _ _ f ▸ is_closed_univ.stable_under_specialization.image h

lemma generalizing_map.stable_under_generalization_image (hf : generalizing_map f) {s : set X}
  (hs : stable_under_generalization s) : stable_under_generalization (f '' s) :=
is_upper_set.image_fibration hf hs

lemma generalizing_map_iff_stable_under_generalization_image :
  generalizing_map f ↔ ∀ s, stable_under_generalization s → stable_under_generalization (f '' s) :=
relation.fibration_iff_is_upper_set_image

alias generalizing_map.stable_under_generalization_image ← stable_under_generalization.image

lemma generalizing_map.stable_under_generalization_range (h : generalizing_map f) :
  stable_under_generalization (range f) :=
@image_univ _ _ f ▸ is_open_univ.stable_under_generalization.image h

