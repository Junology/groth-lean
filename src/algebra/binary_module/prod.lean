import .basic .hom

/-!
 * Constructions and theorems on products of `binary_modules`.
-/

namespace binary_module

open binary_module

local attribute [instance] has_binary_add
attribute [instance] binary_module.has_trivial_init
attribute [instance] model.prod

@[reducible,inline]
definition prod_fst {α β : Type _} [model binary_module α] [model binary_module β] : hom (α×β) α := morphism.proj_fst binary_module

@[reducible,inline]
definition prod_snd {α β : Type _} [model binary_module α] [model binary_module β] : hom (α×β) β := morphism.proj_snd binary_module

@[reducible,inline]
definition prod_inl {α β : Type _} [model binary_module α] [model binary_module β] : hom α (α×β) := @model.prod_inl binary_module binary_module.has_trivial_init α β _ _

@[reducible,inline]
definition prod_inr {α β : Type _} [model binary_module α] [model binary_module β] : hom β (α×β) := @model.prod_inr binary_module binary_module.has_trivial_init α β _ _

lemma pair_is_sum {α β : Type _} [model binary_module α] [model binary_module β] : ∀ (x : α×β), x = (prod_inl.val x.fst) + (prod_inr.val x.snd) :=
  begin
    intros x,
    cases x,
    dsimp [prod_inl,prod_inr],
    dsimp [model.prod_inl,model.prod_inr,has_add.add],
    dsimp [binary_module.add],
    dsimp [premodel.act,prod.map],
    rw [vect.unzip_fst_is_map_fst,vect.unzip_snd_is_map_snd],
    dsimp [vect.map],
    repeat {rw [fixed_elem_is_zero]},
    let hfst := @binary_module.add_zero α _,
    let hsnd := @binary_module.zero_add β _,
    dsimp [binary_module.add] at hfst hsnd,
    rw [hfst,hsnd],
  end

#print axioms pair_is_sum


local infixl `●`:100 := hom.comp

--- Construct `hom (α×β) γ` from `hom α γ` and `hom β γ`.
definition co_zip {α β γ : Type _} [model binary_module α] [model binary_module β] [model binary_module γ] (f : hom α γ) (g : hom β γ) : hom (α×β) γ := (f ● prod_fst) + (g ● prod_snd)

--- Decompose `hom (α×β) γ` into `hom α γ` and `hom β γ`.
definition co_unzip {α β γ : Type _} [model binary_module α] [model binary_module β] [model binary_module γ] (f : hom (α×β) γ) : hom α γ × hom β γ :=
  (f ● prod_inl, f ● prod_inr)

--- `co_zip` after `co_unzip` recovers the original `hom (α×β) γ` pointwisely; i.e. the same as the original up to `funext`.
theorem co_zip_of_co_unzip_ptwise {α β γ : Type _} [model binary_module α] [model binary_module β] [model binary_module γ] (f : hom (α×β) γ) : ∀ x, (co_zip (co_unzip f).fst (co_unzip f).snd).val x = f.val x :=
  begin
    intros x; cases x with a b,
    dsimp [co_zip,co_unzip],
    dsimp [has_add.add,binary_module.add],
    dsimp [premodel.act],
    rw [vect.unzip_fam_eval],
    dsimp [vect.map],
    dsimp [hom.comp,morphism.comp,function.comp],
    let hf := λ x y, f.property ops.add ⁅x,y⁆,
    dunfold vect.map at hf,
    rw [←hf],
    dsimp [prod_fst,morphism.proj_fst,prod_inl,model.prod_inl],
    dsimp [prod_snd,morphism.proj_snd,prod_inr,model.prod_inr],
    csimp only [fixed_elem_is_zero],
    dsimp [premodel.act,prod.map,vect.unzip],
    let hadd_zero := binary_module.add_zero a,
    let hzero_add := binary_module.zero_add b,
    dsimp [binary_module.zero,binary_module.add] at hadd_zero hzero_add,
    rw [hadd_zero,hzero_add]
  end

#print axioms co_zip_of_co_unzip_ptwise

theorem co_unzip_of_co_zip_ptwise {α β γ : Type _} [model binary_module α]  [model binary_module β] [model binary_module γ] (f : hom α γ) (g : hom β γ)  : (∀ a, (co_unzip (co_zip f g)).fst.val a = f.val a) ∧ (∀ b, (co_unzip (co_zip f g)).snd.val b = g.val b) :=
  begin
    split,
    show ∀ (a : α), (co_unzip (co_zip f g)).fst.val a = f.val a, {
      intros a,
      dsimp [co_zip,co_unzip],
      dsimp [hom.comp,morphism.comp,function.comp,subtype.val],
      dsimp [prod_inl,model.prod_inl],
      dsimp [vect.map],
      dsimp [premodel.act,vect.unzip_fam],
      dsimp [prod_fst,prod_snd, morphism.proj_fst, morphism.proj_snd],
      rw [fixed_elem_is_zero,g.property],
      dunfold vect.map,
      let hz := add_zero (f.val a),
      dsimp [binary_module.add,binary_module.zero] at hz,
      rw [hz]
    },
    show ∀ (b : β), (co_unzip (co_zip f g)).snd.val b = g.val b, {
      intros b,
      dsimp [co_zip,co_unzip],
      dsimp [hom.comp,morphism.comp,function.comp,subtype.val],
      dsimp [prod_inr,model.prod_inr],
      dsimp [vect.map],
      dsimp [premodel.act,vect.unzip_fam],
      dsimp [prod_fst,prod_snd, morphism.proj_fst, morphism.proj_snd],
      rw [fixed_elem_is_zero,f.property],
      dunfold vect.map,
      let hz := zero_add (g.val b),
      dsimp [binary_module.add,binary_module.zero] at hz,
      rw [hz]
    }
  end

#print axioms co_unzip_of_co_zip_ptwise

end binary_module
