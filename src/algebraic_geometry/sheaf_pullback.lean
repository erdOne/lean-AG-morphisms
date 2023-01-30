import topology.sheaves.functors
import topology.sheaves.sheaf_condition.sites

namespace Top.sheaf

universes w v u

open category_theory category_theory.limits topological_space

variables (A : Type*) [category.{w} A] [concrete_category.{w} A] [has_colimits A] [has_limits A]
variables [preserves_limits (category_theory.forget A)]
variables [preserves_filtered_colimits (category_theory.forget A)]
variables [reflects_isomorphisms (category_theory.forget A)]

variables {C : Type u} [category.{v} C]
variables {X Y Z : Top.{w}} (f : X ⟶ Y)
variables ⦃ι : Type w⦄ {U : ι → opens Y}

noncomputable theory


lemma pushforward_forget (f : X ⟶ Y) :
  pushforward f ⋙ forget C Y = forget C X ⋙ Top.presheaf.pushforward C f := rfl

/--
Pushforward of sheaves is isomorphic (actually definitionally equal) to pushforward of presheaves.
-/
def pushforward_forget_iso (f : X ⟶ Y) :
  pushforward f ⋙ forget C Y ≅ forget C X ⋙ Top.presheaf.pushforward C f := iso.refl _

variables {C}

@[simp] lemma pushforward_obj_val (f : X ⟶ Y) (F : X.sheaf C) :
  ((pushforward f).obj F).1 = f _* F.1 := rfl

@[simp] lemma pushforward_map (f : X ⟶ Y) {F F' : X.sheaf C} (α : F ⟶ F') :
  ((pushforward f).map α).1 = (Top.presheaf.pushforward C f).map α.1 := rfl

/--
The pushforward functor.
-/
def pullback (f : X ⟶ Y) : Y.sheaf A ⥤ X.sheaf A :=
sites.pushforward A _ _ (opens.map f)

lemma pullback_eq (f : X ⟶ Y) :
  pullback A f = forget A Y ⋙ Top.presheaf.pullback A f ⋙ presheaf_to_Sheaf _ _ := rfl

/--
The pullback of a sheaf is isomorphic (actually definitionally equal) to the sheafification
of the pullback as a presheaf.
-/
def pullback_iso (f : X ⟶ Y) :
  pullback A f ≅ forget A Y ⋙ Top.presheaf.pullback A f ⋙ presheaf_to_Sheaf _ _ := iso.refl _

instance : representably_flat (opens.map f) :=
begin
  constructor,
  intro U,
  apply_with is_cofiltered.mk { instances := ff },
  constructor,
  { intros V W,
    refine ⟨⟨⟨punit.star⟩, V.right ⊓ W.right, hom_of_le $ le_inf V.hom.le W.hom.le⟩,
      { right := hom_of_le inf_le_left }, { right := hom_of_le inf_le_right }, trivial⟩ },
  { intros U V i j, refine ⟨_, 𝟙 _, by ext; congr⟩ },
  { exact ⟨structured_arrow.mk $ show U ⟶ (opens.map f).obj ⊤, from hom_of_le le_top⟩ },
end

lemma compatible_preserving_opens_map :
  compatible_preserving (opens.grothendieck_topology X) (opens.map f) :=
compatible_preserving_of_flat _ _

lemma cover_preserving_opens_map :
  cover_preserving (opens.grothendieck_topology Y)
    (opens.grothendieck_topology X) (opens.map f) :=
begin
  constructor,
  intros U S hS x hx,
  obtain ⟨V, i, hi, hxV⟩ := hS (f x) hx,
  exact ⟨_, (opens.map f).map i, ⟨_, _, 𝟙 _, hi, subsingleton.elim _ _⟩, hxV⟩
end

/-- The adjunction between pullback and pushforward for sheaves on topological spaces. -/
def pullback_pushforward_adjunction (f : X ⟶ Y) :
  pullback A f ⊣ pushforward f :=
sites.pullback_pushforward_adjunction _ _ _ (compatible_preserving_opens_map f)
  (cover_preserving_opens_map f)

instance : is_left_adjoint (pullback A f) := ⟨_, pullback_pushforward_adjunction A f⟩
instance : is_right_adjoint (pushforward f : X.sheaf A ⥤ Y.sheaf A) :=
⟨_, pullback_pushforward_adjunction A f⟩

variables (g : Y ⟶ Z) 

noncomputable!
def pushforward_comp :
  pushforward f ⋙ pushforward g ≅ (pushforward (f ≫ g) : X.sheaf C ⥤ Z.sheaf C) :=
iso.refl _

noncomputable!
def pullback_comp :
  pullback A g ⋙ pullback A f ≅ pullback A (f ≫ g) :=
adjunction.nat_iso_of_right_adjoint_nat_iso
  ((pullback_pushforward_adjunction A g).comp (pullback_pushforward_adjunction A f))
  (pullback_pushforward_adjunction A (f ≫ g)) (pushforward_comp f g)

def pullback_congr {f g : X ⟶ Y} (e : f = g) :
  pullback A f ≅ pullback A g :=
eq_to_iso (by subst e)

end Top.sheaf