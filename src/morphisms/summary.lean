import morphisms.valuative_criterion
import for_mathlib.pullback_mono

/-!

# Summary of this repository

-/

namespace algebraic_geometry

open _root_.category_theory.morphism_property morphism_property (topologically)

open _root_.category_theory (is_iso)

open function (injective surjective bijective)

/- QoL definitions -/

universe u

variables {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

local infix (name := impl) `⇒`      := @has_le.le (category_theory.morphism_property Scheme) _
local infix (name := and) `+`        := @has_inf.inf (category_theory.morphism_property Scheme) _

local notation `@is_iso`             := @category_theory.is_iso Scheme _
local notation `@mono`               := @category_theory.mono Scheme _
local notation `is_local_at_target`  := property_is_local_at_target
local notation `ring_hom.surjective` := λ R S _ _ f, function.surjective f
local notation `ring_hom.integral`   := λ R S _ _ f, by exactI ring_hom.is_integral f
local notation `qcqs`                := @quasi_compact + @quasi_separated

def Scheme.has_coe_to_sort : has_coe_to_sort Scheme Type* := ⟨λ X, X.carrier⟩
def Scheme.has_coe_to_fun : has_coe_to_fun (X ⟶ Y) (λ _, X.carrier → Y.carrier) := ⟨λ f, f.1.base⟩
local attribute [reducible, instance] Scheme.has_coe_to_sort Scheme.has_coe_to_fun

noncomputable
abbreviation Scheme.hom.stalk_map {X Y : Scheme} (f : X ⟶ Y) := PresheafedSpace.stalk_map f.1

meta def show_impl := `[intros X Y f hf, exactI infer_instance]

/- end QoL definitions -/

/-! # Isomorphisms -/

example : is_iso f ↔ is_iso f.1.base ∧ ∀ x, category_theory.is_iso (f.stalk_map x)                  := is_iso_iff_stalk

example : is_local_at_target       @is_iso := is_iso_is_local_at_target
example : stable_under_composition @is_iso := λ _ _ _ f g _ _, by exactI infer_instance
example : stable_under_base_change @is_iso := λ _ _ _ _ _ _ _ _ H _, by exactI H.is_iso_right

/-! # Monomorphisms -/

example : @mono = diagonal @is_iso := mono_eq_diagonal

example : is_local_at_target       @mono := mono_is_local_at_target
example : stable_under_composition @mono := λ _ _ _ f g _ _, by exactI category_theory.mono_comp f g
example : stable_under_base_change @mono := λ _ _ _ _ _ _ _ _ H _, by exactI H.mono_right

example : @is_iso                 ⇒ @mono := by show_impl
example : @is_open_immersion      ⇒ @mono := by show_impl
example : @is_closed_immersion    ⇒ @mono := by show_impl
example : @is_immersion           ⇒ @mono := by show_impl

/-! # Surjective morphisms -/

example : is_local_at_target       @surjective := surjective_is_local_at_target
example : stable_under_composition @surjective := surjective_stable_under_composition
example : stable_under_base_change @surjective := surjective_stable_under_base_change

example : @is_iso                 ⇒ @surjective := by show_impl

/-! # Radicial morphisms -/

/-!
```lean
class radicial (f : X ⟶ Y) : Prop :=
(base_injective [] : function.injective f.1.base)
(residue_radicial [] : ∀ x, ring_hom.is_radicial (f.map_residue_field x))
```

Disclaimer: radicial extensions are defined to be epimorphisms in the category of fields,
since we do not have results on purely inseparable extensions yet.
-/
example : @radicial = diagonal @surjective                                                          := radicial_eq_diagonal_surjective
example : @radicial = universally morphism_property.injective                                       := radicial_eq_univerally_injective 

example : is_local_at_target       @radicial := radicial_is_local_at_target
example : stable_under_composition @radicial := radicial_stable_under_composition
example : stable_under_base_change @radicial := radicial_stable_under_base_change

example : @is_iso                 ⇒ @radicial := by show_impl
example : @mono                   ⇒ @radicial := by show_impl
example : @is_open_immersion      ⇒ @radicial := by show_impl
example : @is_closed_immersion    ⇒ @radicial := by show_impl
example : @is_immersion           ⇒ @radicial := by show_impl

/-! # Quasi-compact morphisms -/

/-!
```lean
class quasi_compact (f : X ⟶ Y) : Prop :=
(is_compact_preimage : ∀ U : set Y.carrier, is_open U → is_compact U → is_compact (f.1.base ⁻¹' U))
```
-/
example : @quasi_compact = target_affine_locally (λ X Y f _, compact_space X)                       := quasi_compact_eq_affine_property

example : is_local_at_target       @quasi_compact := quasi_compact.is_local_at_target
example : stable_under_composition @quasi_compact := quasi_compact_stable_under_composition
example : stable_under_base_change @quasi_compact := quasi_compact_stable_under_base_change

example : @is_iso                 ⇒ @quasi_compact := by show_impl
example : @affine                 ⇒ @quasi_compact := by show_impl
example : @is_closed_immersion    ⇒ @quasi_compact := by show_impl
example : @integral               ⇒ @quasi_compact := by show_impl
example : @finite                 ⇒ @quasi_compact := by show_impl
example : @universally_closed     ⇒ @quasi_compact := by show_impl
example : @proper                 ⇒ @quasi_compact := by show_impl

example [quasi_compact (f ≫ g)] [quasi_separated g] : quasi_compact f := quasi_compact_of_comp f g
example [quasi_compact (f ≫ g)] [surjective f] : quasi_compact g := quasi_compact_of_comp_surjective f g

/-! # Quasi-separated morphisms -/

/-!
```lean
class quasi_separated (f : X ⟶ Y) : Prop :=
(diagonal_quasi_compact : quasi_compact (pullback.diagonal f))
```
-/
example : @quasi_separated = diagonal @quasi_compact                                                := quasi_separated_eq_diagonal_is_quasi_compact
example : @quasi_separated = target_affine_locally (λ X Y f _, quasi_separated_space X)             := quasi_separated_eq_affine_property

example : is_local_at_target       @quasi_separated := quasi_separated.is_local_at_target
example : stable_under_composition @quasi_separated := quasi_separated_stable_under_composition
example : stable_under_base_change @quasi_separated := quasi_separated_stable_under_base_change

example : @is_iso                 ⇒ @quasi_separated := by show_impl
example : @mono                   ⇒ @quasi_separated := by show_impl
example : @radicial               ⇒ @quasi_separated := by show_impl
example : @affine                 ⇒ @quasi_separated := by show_impl
example : @is_open_immersion      ⇒ @quasi_separated := by show_impl
example : @is_closed_immersion    ⇒ @quasi_separated := by show_impl
example : @is_immersion           ⇒ @quasi_separated := by show_impl
example : @separated              ⇒ @quasi_separated := by show_impl
example : @integral               ⇒ @quasi_separated := by show_impl
example : @finite                 ⇒ @quasi_separated := by show_impl
example : @proper                 ⇒ @quasi_separated := by show_impl

example [quasi_separated (f ≫ g)] : quasi_separated f := quasi_separated_of_comp f g

/-! # Affine morphisms -/

/-!
```lean
class affine (f : X ⟶ Y) : Prop :=
(is_affine_preimage : ∀ U : opens Y.carrier,
  is_affine_open U → is_affine_open ((opens.map f.1.base).obj U))
```
-/
example : @affine = target_affine_locally (λ X Y f _, is_affine X)                                  := affine_eq_affine_property

example : is_local_at_target       @affine := affine_is_local_at_target
example : stable_under_composition @affine := affine_stable_under_composition
example : stable_under_base_change @affine := affine_stable_under_base_change

example : @is_iso                 ⇒ @affine := by show_impl
example : @is_closed_immersion    ⇒ @affine := by show_impl
example : @integral               ⇒ @affine := by show_impl
example : @finite                 ⇒ @affine := by show_impl

/-! # Open immersions -/

/-!
```lean
class is_open_immersion (f : X ⟶ Y) : Prop :=
(base_open : open_embedding f)
(c_iso : ∀ U : opens X, is_iso (f.c.app (op (base_open.is_open_map.functor.obj U))))
```

Disclaimer: It is actually defined on all morphsms between presheaved spaces instead, but it is 
definitionally equal to the above for Schemes.
-/
example : is_open_immersion f ↔ open_embedding f ∧ ∀ x, is_iso (f.stalk_map x)                     := is_open_immersion_iff_stalk

example : is_local_at_target       @is_open_immersion := is_open_immersion_is_local_at_target
example : stable_under_composition @is_open_immersion := is_open_immersion_stable_under_composition
example : stable_under_base_change @is_open_immersion := is_open_immersion_stable_under_base_change

example : @is_iso                 ⇒ @is_open_immersion := by show_impl

/-! # Closed immersions -/

/-!
```lean
class is_closed_immersion (f : X ⟶ Y) : Prop :=
(base_closed [] : closed_embedding f)
(c_locally_surjective [] : Top.presheaf.is_locally_surjective f.1.c)
```
-/
example : is_closed_immersion f ↔ closed_embedding f ∧ ∀ x, function.surjective (f.stalk_map x)     := is_closed_immersion_iff_stalk
example : @is_closed_immersion = target_affine_locally (affine_and ring_hom.surjective)             := is_closed_immersion_eq_affine_property
example : @is_closed_immersion = @finite + @mono                                                    := is_closed_immersion_eq_finite_inf_mono

example : is_local_at_target       @is_closed_immersion := is_closed_immersion_is_local_at_target
example : stable_under_composition @is_closed_immersion := is_closed_immersion_stable_under_composition
example : stable_under_base_change @is_closed_immersion := is_closed_immersion_stable_under_base_change

example : @is_iso                 ⇒ @is_closed_immersion := by show_impl

/-! # Immersions -/

/-!
```lean
class is_immersion (f : X ⟶ Y) : Prop :=
(base_embedding [] : embedding f)
(range_is_locally_closed [] : is_locally_closed (set.range f))
(stalk_map_surjective [] : ∀ x, surjective (f.stalk_map x))
```

This is different but equivalent to the usual definition. See the example below
-/
example : is_immersion f ↔
  ∃ Z (g : X ⟶ Z) [is_closed_immersion g] (h : Z ⟶ Y) [is_open_immersion h], g ≫ h = f :=
is_immersion_iff_exists_factor f

example : is_local_at_target       @is_immersion := is_immersion_is_local_at_target
example : stable_under_composition @is_immersion := is_immersion_stable_under_composition
example : stable_under_base_change @is_immersion := is_immersion_stable_under_base_change

example : @is_iso                 ⇒ @is_immersion := by show_impl
example : @is_open_immersion      ⇒ @is_immersion := by show_impl
example : @is_closed_immersion    ⇒ @is_immersion := by show_impl

/-! # Separated morphisms -/

/-!
```lean
class separated (f : X ⟶ Y) : Prop :=
(diagonal_is_closed_immersion : is_closed_immersion (pullback.diagonal f))
```
-/
example : @separated = target_affine_locally (λ X Y f _, is_separated X)                            := separated_eq_affine_property
example : @separated = @quasi_separated + valuative_criterion.uniqueness                            := separated_eq_valuative_criterion

example : is_local_at_target       @separated := separated.is_local_at_target
example : stable_under_composition @separated := separated_stable_under_composition
example : stable_under_base_change @separated := separated_stable_under_base_change

example : @is_iso                 ⇒ @separated := by show_impl
example : @mono                   ⇒ @separated := by show_impl
example : @radicial               ⇒ @separated := by show_impl
example : @affine                 ⇒ @separated := by show_impl
example : @is_open_immersion      ⇒ @separated := by show_impl
example : @is_closed_immersion    ⇒ @separated := by show_impl
example : @is_immersion           ⇒ @separated := by show_impl
example : @integral               ⇒ @separated := by show_impl
example : @finite                 ⇒ @separated := by show_impl
example : @proper                 ⇒ @separated := by show_impl

/-! # Locally of finite type morphisms -/

/-!
```lean
class locally_of_finite_type (f : X ⟶ Y) : Prop :=
(finite_type_of_affine_subset :
  ∀ (U : Y.affine_opens) (V : X.affine_opens) (e : V.1 ≤ (opens.map f.1.base).obj U.1),
  (f.app_le e).finite_type)
```
-/
example : @locally_of_finite_type = affine_locally @ring_hom.finite_type                            := locally_of_finite_type_eq

example : is_local_at_target       @locally_of_finite_type := locally_of_finite_type_is_local_at_target
example : stable_under_composition @locally_of_finite_type := locally_of_finite_type_stable_under_composition
example : stable_under_base_change @locally_of_finite_type := locally_of_finite_type_stable_under_base_change

example : @is_iso                 ⇒ @locally_of_finite_type := by show_impl
example : @is_open_immersion      ⇒ @locally_of_finite_type := by show_impl
example : @is_closed_immersion    ⇒ @locally_of_finite_type := by show_impl
example : @is_immersion           ⇒ @locally_of_finite_type := by show_impl
example : @finite                 ⇒ @locally_of_finite_type := by show_impl
example : @proper                 ⇒ @locally_of_finite_type := by show_impl

/-! # Integral morphisms -/

/-!
```lean
class integral (f : X ⟶ Y) extends affine f : Prop :=
(is_integral_of_affine [] :
  ∀ U : opens Y.carrier, is_affine_open U → (f.1.c.app (op U)).is_integral)
```
-/
example : @integral = target_affine_locally (affine_and ring_hom.integral)                          := integral_eq_affine_property
example : @integral = @affine + @universally_closed                                                 := integral_eq_affine_inf_universally_closed

example : is_local_at_target       @integral := integral_is_local_at_target
example : stable_under_composition @integral := integral_stable_under_composition
example : stable_under_base_change @integral := integral_stable_under_base_change

example : @is_iso                 ⇒ @integral := by show_impl
example : @is_closed_immersion    ⇒ @integral := by show_impl
example : @finite                 ⇒ @integral := by show_impl

/-! # Finite morphisms -/

/-!
```lean
class finite (f : X ⟶ Y) extends affine f : Prop :=
(is_finite_of_affine : ∀ U : opens Y.carrier, is_affine_open U → (f.1.c.app (op U)).finite)
```
-/
example : @finite = target_affine_locally (affine_and @ring_hom.finite)                             := finite_eq_affine_property
example : @finite = @proper + @affine                                                               := finite_eq_proper_inf_affine
example : @finite = @integral + @locally_of_finite_type                                             := finite_eq_integral_inf_locally_of_finite_type

example : is_local_at_target       @finite := finite_is_local_at_target
example : stable_under_composition @finite := finite_stable_under_composition
example : stable_under_base_change @finite := finite_stable_under_base_change

example : @is_iso                 ⇒ @finite := by show_impl
example : @is_closed_immersion    ⇒ @finite := by show_impl

/-! # Universally specializing morphisms -/

/-!
This is only for the valuative criterion. 
-/
example : valuative_criterion.existence = universally (topologically @specializing_map)             := valuative_criterion.existence_eq

/-! # Universally closed morphisms -/

/-!
```lean
class universally_closed (f : X ⟶ Y) : Prop :=
(out : universally (topologically @is_closed_map) f)
```
-/
example : @universally_closed = universally (topologically @is_closed_map)                          := universally_closed_eq
example : @universally_closed = @quasi_compact + universally (topologically @specializing_map)      := universally_closed_eq_quasi_compact_and_universally_specializing
example : @universally_closed = @quasi_compact + valuative_criterion.existence                      := universally_closed_eq_valuative_criterion

example : is_local_at_target       @universally_closed := universally_closed_is_local_at_target
example : stable_under_composition @universally_closed := universally_closed_stable_under_composition
example : stable_under_base_change @universally_closed := universally_closed_stable_under_base_change

example : @is_iso                 ⇒ @universally_closed := by show_impl
example : @is_closed_immersion    ⇒ @universally_closed := by show_impl
example : @integral               ⇒ @universally_closed := by show_impl
example : @finite                 ⇒ @universally_closed := by show_impl
example : @proper                 ⇒ @universally_closed := by show_impl

/-! # Proper morphisms -/

/-!
```lean
class proper extends separated f, universally_closed f, locally_of_finite_type f : Prop.
```
-/
example : @proper = @separated + @universally_closed + @locally_of_finite_type                      := proper_eq
example : @proper = qcqs + @locally_of_finite_type + valuative_criterion                            := proper_eq_valuative_criterion

example : is_local_at_target       @proper := proper_is_local_at_target
example : stable_under_composition @proper := proper_stable_under_composition
example : stable_under_base_change @proper := proper_stable_under_base_change

example : @is_iso                 ⇒ @proper := by show_impl
example : @is_closed_immersion    ⇒ @proper := by show_impl
example : @finite                 ⇒ @proper := by show_impl

end algebraic_geometry