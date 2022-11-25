import category_theory.limits.shapes.pullbacks

namespace category_theory

open limits

noncomputable theory

variables {C : Type*} [category C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [has_pullback (f ≫ g) g]

def pullback.lift_comp :=
pullback.lift (𝟙 _) f (category.id_comp $ f ≫ g)

@[simp, reassoc]
lemma pullback.lift_comp_fst : pullback.lift_comp f g ≫ pullback.fst = 𝟙 _ :=
pullback.lift_fst _ _ _

lemma pullback.lift_comp_snd : pullback.lift_comp f g ≫ pullback.snd = f :=
pullback.lift_snd _ _ _

instance : is_split_mono (pullback.lift_comp f g) :=
⟨⟨⟨_, pullback.lift_comp_fst f g⟩⟩⟩ 

local attribute [instance] has_pullback_of_right_iso

lemma pullback.fst_lift_comp_has_pullback_aux :
  has_pullback (f ≫ g) (𝟙 Y ≫ g) :=
by rwa category.id_comp

local attribute [instance] pullback.fst_lift_comp_has_pullback_aux

lemma pullback.fst_lift_comp :
  pullback.fst ≫ pullback.lift_comp f g =
    pullback.map_desc f (𝟙 _) g ≫ (pullback.congr_hom rfl (category.id_comp _)).hom :=
begin
  apply pullback.hom_ext; simp only [pullback.congr_hom_hom, pullback.lift_fst,
    pullback.lift_snd, category.assoc, category.comp_id, pullback.condition, pullback.lift_comp],
end

def pullback.lift_comp_iso_map_desc : 
  arrow.mk (pullback.lift_comp f g) ≅ arrow.mk (pullback.map_desc f (𝟙 _) g) :=
(arrow.iso_mk' _ _ (as_iso pullback.fst : _) (pullback.congr_hom rfl (category.id_comp _))
  (pullback.fst_lift_comp f g)).symm

end category_theory