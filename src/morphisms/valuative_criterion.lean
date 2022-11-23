import morphisms.universally_closed
import ring_theory.valuation.valuation_ring

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universes v u

namespace algebraic_geometry

variables {X Y : Scheme.{u}} (f : X ⟶ Y)

open category_theory.morphism_property
open algebraic_geometry.morphism_property (topologically)

structure valuative_comm_sq {X Y : Scheme.{u}} (f : X ⟶ Y) :=
(R : Type.{u})
[hR : comm_ring R]
[hR₁ : is_domain R]
[hR₂ : valuation_ring R]
(i₁ : Scheme.Spec.obj (op $ CommRing.of $ fraction_ring R) ⟶ X)
(i₂ : Scheme.Spec.obj (op $ CommRing.of R) ⟶ Y)
(comm_sq : comm_sq i₁ (Scheme.Spec.map (CommRing.of_hom $ algebra_map R (fraction_ring R)).op) f i₂)
.
def valuative_criterion.existence : morphism_property Scheme :=
λ X Y f, ∀ S : valuative_comm_sq f, S.comm_sq.has_lift

def valuative_criterion.uniqueness : morphism_property Scheme :=
λ X Y f, ∀ S : valuative_comm_sq f, subsingleton S.comm_sq.lift_struct

def valuative_criterion : morphism_property Scheme :=
λ X Y f, ∀ S : valuative_comm_sq f, nonempty (unique (S.comm_sq.lift_struct))

section existence

lemma valuative_criterion.existence.specializing_map (h : valuative_criterion.existence f) :
  specializing_map f.1.base :=
begin

end

end existence



end algebraic_geometry