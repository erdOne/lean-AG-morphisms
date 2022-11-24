import topology.sheaves.stalks
import category_theory.category.galois_connection

section inducing

open topological_space category_theory

universe u

variables {X Y : Top.{u}} {f : X ⟶ Y}

/-- Given an inducing map `X ⟶ Y` and some `U : opens X`, this is the union of all open sets
whose preimage is `U`. This is right adjoint to `opens.map`. -/
@[nolint unused_arguments]
def inducing.functor_obj {X Y : Top} {f : X ⟶ Y} (hf : inducing f) (U : opens X) : opens Y :=
Sup { s : opens Y | (topological_space.opens.map f).obj s = U }

lemma inducing.obj_functor_obj {X Y : Top} {f : X ⟶ Y} (hf : inducing f) (U : opens X) :
  (topological_space.opens.map f).obj (hf.functor_obj U) = U :=
begin
  apply le_antisymm,
  { rintros x ⟨_, ⟨s, rfl⟩, _, ⟨rfl : _ = U, rfl⟩, hx : f x ∈ s⟩, exact hx },
  { intros x hx, obtain ⟨U, hU⟩ := U, obtain ⟨t, ht, rfl⟩ := hf.is_open_iff.mp hU,
    exact opens.mem_Sup.mpr ⟨⟨_, ht⟩, rfl, hx⟩ }
end

lemma inducing.mem_functor_obj_iff {X Y : Top} {f : X ⟶ Y} (hf : inducing f) (U : opens X)
  {x : X} : f x ∈ hf.functor_obj U ↔ x ∈ U :=
by { conv_rhs { rw ← hf.obj_functor_obj U }, refl }

lemma inducing.le_functor_obj_iff {X Y : Top} {f : X ⟶ Y} (hf : inducing f) {U : opens X}
  {V : opens Y} : V ≤ hf.functor_obj U ↔ (topological_space.opens.map f).obj V ≤ U :=
begin
  obtain ⟨U, hU⟩ := U,
  obtain ⟨t, ht, rfl⟩ := hf.is_open_iff.mp hU,
  split,
  { exact λ i x hx,
      (hf.mem_functor_obj_iff ((topological_space.opens.map f).obj ⟨t, ht⟩)).mp (i hx) },
  { intros h x hx,
    refine opens.mem_Sup.mpr ⟨⟨_, V.2.union ht⟩, opens.ext _, set.mem_union_left t hx⟩,
    dsimp,
    rwa [set.union_eq_right_iff_subset] },
end

/--
An inducing map `f : X ⟶ Y` induces an galois insertion between `opens Y` and `opens X`.
-/
def inducing.opens_gi {X Y : Top} {f : X ⟶ Y} (hf : inducing f) :
  galois_insertion (topological_space.opens.map f).obj hf.functor_obj  :=
⟨_, λ _ _, hf.le_functor_obj_iff.symm, λ U, (hf.obj_functor_obj U).ge, λ _ _, rfl⟩

/--
An inducing map `f : X ⟶ Y` induces a functor `opens X ⥤ opens Y`.
-/
@[simps]
def inducing.functor {X Y : Top} {f : X ⟶ Y} (hf : inducing f) :
  opens X ⥤ opens Y :=
{ obj := λ U, Sup { s : opens Y | (topological_space.opens.map f).obj s = U },
  map := λ U V h, hom_of_le (hf.le_functor_obj_iff.mpr ((hf.obj_functor_obj U).trans_le h.le)) }

/--
An inducing map `f : X ⟶ Y` induces an adjunction between `opens Y` and `opens X`.
-/
def inducing.adjunction {X Y : Top} {f : X ⟶ Y} (hf : inducing f) :
  adjunction (topological_space.opens.map f) hf.functor :=
hf.opens_gi.gc.adjunction

/--
An open map `f : X ⟶ Y` induces a functor `open_nhds x ⥤ open_nhds (f x)`.
-/
@[simps]
def inducing.functor_nhds (h : inducing f) (x : X) :
  open_nhds x ⥤ open_nhds (f x) :=
{ obj := λ U, ⟨h.functor.obj U.1, (h.mem_functor_obj_iff U.1).mpr U.2⟩,
  map := λ U V i, h.functor.map i }

/--
An open map `f : X ⟶ Y` induces an adjunction between `open_nhds x` and `open_nhds (f x)`.
-/
def inducing.adjunction_nhds (h : inducing f) (x : X) :
  open_nhds.map f x ⊣ h.functor_nhds x :=
adjunction.mk_of_unit_counit
{ unit := { app := λ U, hom_of_le (h.adjunction.unit.app U.1).le },
  counit := { app := λ V, hom_of_le (h.adjunction.counit.app V.1).le } }

end inducing

open category_theory category_theory.limits topological_space Top.presheaf

lemma Top.presheaf.stalk_pushforward_iso_of_inducing {C} [category C] [has_colimits C]
  {X Y : Top} {f : X ⟶ Y}
  (hf : inducing f) (F : X.presheaf C) (x : X) : is_iso (F.stalk_pushforward _ f x) :=
begin
  haveI := functor.initial_of_adjunction (hf.adjunction_nhds x),
  convert is_iso.of_iso (functor.final.colimit_iso (open_nhds.map f x).op
    ((open_nhds.inclusion x).op ⋙ F)),
  { apply stalk_hom_ext,
    intros U hU,
    refine (stalk_pushforward_germ _ f F _ ⟨x, hU⟩).trans _,
    symmetry,
    exact colimit.ι_pre ((open_nhds.inclusion x).op ⋙ F) (open_nhds.map f x).op _ },
end