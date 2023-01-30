-- import morphisms.immersion
-- .

-- open category_theory category_theory.limits

-- namespace algebraic_geometry

-- universe u

-- variables {X Y S : LocallyRingedSpace.{u}} (f : X ⟶ S) (g : Y ⟶ S)

-- instance : has_limits (SheafedSpace CommRing) := sorry
-- instance : preserves_limits (SheafedSpace.forget CommRing) := sorry 

-- def SheafedSpace.pullback_cone.X {C : Type*} [category C] 
--   {X Y S : SheafedSpace C} (f : X ⟶ S) (g : Y ⟶ S) : SheafedSpace C :=
-- { carrier := Top.of { x : X × Y | f x.1 = g x.2 },
--   presheaf := _,
--   is_sheaf := begin
    
--   end }

-- def SheafedSpace.pullback_cone {C : Type*} [category C] 
--   {X Y S : SheafedSpace C} (f : X ⟶ S) (g : Y ⟶ S) : pullback_cone f g :=
-- pullback_cone.mk _ _ _


-- noncomputable
-- def pullback_of_stalk_surjective 
--   (hf : ∀ x : X.carrier, function.surjective (PresheafedSpace.stalk_map f.1 x)) :
--   LocallyRingedSpace :=
-- { local_ring := begin
--     intro x,

--   end,
--   ..(pullback f.1 g.1 : _) },



-- end algebraic_geometry