import morphisms.separated
import morphisms.integral


open category_theory category_theory.limits

namespace algebraic_geometry

universe u

variables {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

@[mk_iff]
class proper extends separated f, universally_closed f, locally_of_finite_type f : Prop.

example [proper f] : quasi_compact f := infer_instance

lemma proper_eq : @proper = @separated ⊓ @universally_closed ⊓ @locally_of_finite_type :=
by { ext, rw [proper_iff, ← and_assoc], refl }

instance [proper f] [proper g] : proper (f ≫ g) := ⟨⟩

lemma proper_stable_under_composition : 
  morphism_property.stable_under_composition @proper :=
λ _ _ _ _ _ _ _, by exactI infer_instance

instance finite.to_proper [finite f] : proper f := ⟨⟩

lemma proper_respects_iso :
  morphism_property.respects_iso @proper :=
proper_stable_under_composition.respects_iso (λ _ _ _, ⟨⟩)

lemma proper_is_local_at_target :
  property_is_local_at_target @proper :=
begin
  rw proper_eq,
  exact (separated.is_local_at_target.inf universally_closed_is_local_at_target).inf 
    locally_of_finite_type_is_local_at_target,
end

lemma proper_stable_under_base_change :
  morphism_property.stable_under_base_change @proper :=
begin
  introsI X Y Y' S f g f' g' H Hg,
  exact @@proper.mk (separated_stable_under_base_change H infer_instance)
    (universally_closed_stable_under_base_change H infer_instance)
    (locally_of_finite_type_stable_under_base_change H infer_instance),
end

lemma finite_eq_proper_inf_affine :
  @finite = @proper ⊓ @affine :=
begin
  rw [proper_eq, finite_eq_integral_inf_locally_of_finite_type,
    integral_eq_affine_inf_universally_closed],
  conv_lhs { rw [← inf_eq_right.mpr affine_le_separated] },
  simp only [inf_comm, inf_assoc, inf_left_comm],
end

lemma proper.open_cover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.open_cover.{u} Y)
  (f : X ⟶ Y) :
  proper f ↔ ∀ i, proper (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
proper_is_local_at_target.open_cover_iff f 𝒰

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [proper g] :
  proper (pullback.fst : pullback f g ⟶ X) :=
proper_stable_under_base_change.fst f g infer_instance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [proper f] :
  proper (pullback.snd : pullback f g ⟶ Y) :=
proper_stable_under_base_change.snd f g infer_instance


lemma universally_closed.of_comp [universally_closed (f ≫ g)] [separated g] :
  universally_closed f := 
by { rw [← pullback.lift_comp_snd f g], apply_instance }

lemma proper.of_comp [proper (f ≫ g)] [separated g] : proper f := 
by { rw [← pullback.lift_comp_snd f g], apply_instance }

end algebraic_geometry