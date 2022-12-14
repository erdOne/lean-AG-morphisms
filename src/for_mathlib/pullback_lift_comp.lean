import category_theory.limits.shapes.pullbacks

namespace category_theory

open limits

noncomputable theory

variables {C : Type*} [category C] {X Y Z : C} (f : X ā¶ Y) (g : Y ā¶ Z) [has_pullback (f ā« g) g]

def pullback.lift_comp :=
pullback.lift (š _) f (category.id_comp $ f ā« g)

@[simp, reassoc]
lemma pullback.lift_comp_fst : pullback.lift_comp f g ā« pullback.fst = š _ :=
pullback.lift_fst _ _ _

lemma pullback.lift_comp_snd : pullback.lift_comp f g ā« pullback.snd = f :=
pullback.lift_snd _ _ _

instance : is_split_mono (pullback.lift_comp f g) :=
āØāØāØ_, pullback.lift_comp_fst f gā©ā©ā© 

local attribute [instance] has_pullback_of_right_iso

lemma pullback.fst_lift_comp_has_pullback_aux :
  has_pullback (f ā« g) (š Y ā« g) :=
by rwa category.id_comp

local attribute [instance] pullback.fst_lift_comp_has_pullback_aux

lemma pullback.fst_lift_comp :
  pullback.fst ā« pullback.lift_comp f g =
    pullback.map_desc f (š _) g ā« (pullback.congr_hom rfl (category.id_comp _)).hom :=
begin
  apply pullback.hom_ext; simp only [pullback.congr_hom_hom, pullback.lift_fst,
    pullback.lift_snd, category.assoc, category.comp_id, pullback.condition, pullback.lift_comp],
end

def pullback.lift_comp_iso_map_desc : 
  arrow.mk (pullback.lift_comp f g) ā arrow.mk (pullback.map_desc f (š _) g) :=
(arrow.iso_mk' _ _ (as_iso pullback.fst : _) (pullback.congr_hom rfl (category.id_comp _))
  (pullback.fst_lift_comp f g)).symm

end category_theory