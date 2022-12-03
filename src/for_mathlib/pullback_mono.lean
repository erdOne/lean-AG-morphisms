import category_theory.limits.shapes.comm_sq

namespace category_theory

open limits

variables {C : Type*} [category C]
variables {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} 

lemma is_pullback.is_iso_right (H : is_pullback f g h i) [is_iso h] : is_iso g :=
begin
  have : _ ≫ 𝟙 _ = g := H.is_limit.cone_point_unique_up_to_iso_hom_comp
    (pullback_cone_of_left_iso_is_limit h i) walking_cospan.right,
  rw ← this,
  apply_instance
end

lemma is_pullback.is_iso_left (H : is_pullback f g h i) [is_iso i] : is_iso f :=
H.flip.is_iso_right

lemma is_pullback.mono_left (H : is_pullback f g h i) [mono i] : mono f :=
pullback_cone.mono_fst_of_is_pullback_of_mono H.is_limit

lemma is_pullback.mono_right (H : is_pullback f g h i) [mono h] : mono g :=
pullback_cone.mono_snd_of_is_pullback_of_mono H.is_limit

end category_theory