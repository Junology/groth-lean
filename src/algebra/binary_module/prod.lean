import .basic

/-!
 * Constructions and theorems on products of `binary_modules`.
-/

namespace binary_module

local attribute [instance] has_binary_add
attribute [instance] binary_module.has_trivial_init

definition prod_inl {α β : Type _} [model binary_module α] [model binary_module β] : morphism binary_module α (α×β) := @model.prod_inl binary_module binary_module.has_trivial_init α β _ _

definition prod_inr {α β : Type _} [model binary_module α] [model binary_module β] : morphism binary_module β (α×β) := @model.prod_inr binary_module binary_module.has_trivial_init α β _ _

lemma pair_is_sum {α β : Type _} [model binary_module α] [model binary_module β] : ∀ (x : α×β), x = (prod_inl x.fst) + (prod_inr x.snd) :=
  begin
    intros x,
    cases x,
    dsimp [prod_inl,prod_inr],
    dsimp [model.prod_inl,model.prod_inr,has_add.add],
    dsimp [binary_module.add],
    dsimp [premodel.act,prod.map],
    rw [vect.unzip_fst_is_map_fst,vect.unzip_snd_is_map_snd],
    dsimp [vect.map],
    unfold coe_fn,
    unfold has_coe_to_fun.coe,
    dsimp *,
    repeat {rw [fixed_elem_is_zero]},
    let hfst := @binary_module.add_zero α _,
    let hsnd := @binary_module.zero_add β _,
    dsimp [binary_module.add] at hfst hsnd,
    rw [hfst,hsnd],
  end

#print axioms pair_is_sum


local infixl `●`:100 := morphism.comp

lemma co_unzip {α β γ : Type _} [model binary_module α] [model binary_module β] [model binary_module γ] (f : morphism binary_module (α×β) γ) : morphism binary_module α γ × morphism binary_module β γ :=
  (f ● prod_inl, f ● prod_inr)

end binary_module
