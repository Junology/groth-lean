import algebra.theory.free
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


/-!
 * Proof of the fact that the product of models of `binary_module` is simultaneously a coproduct.
--/

section

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

end


/-!
 * Proof of the fact that the (co)product of free models of `binary_module` is again free.
--/

section

universe u

variables {α β : Sort _}
variables {φ ψ : Type _} [model binary_module φ] [model binary_module ψ]
variables (ja : α → φ) (jb : β → ψ)

local infixl `●`:100 := hom.comp

definition basis_sum : psum α β → φ×ψ
| (psum.inl a) := (ja a, binary_module.zero ψ)
| (psum.inr b) := (binary_module.zero φ, jb b)

--- the (co)product of free models of `binary_module` is again free.
theorem prod_free (ha : is_free.{u} binary_module ja) (hb : is_free.{u} binary_module jb) : is_free.{u} binary_module (basis_sum ja jb) :=
  begin
    intros γ mc f,
    let hfa := @ha γ mc (λ a, f (psum.inl a)),
    let hfb := @hb γ mc (λ b, f (psum.inr b)),
    cases h₁: hfa with f₁ hf₁,
    cases h₂: hfb with f₂ hf₂,
    existsi @co_zip φ ψ γ _ _ mc f₁ f₂,
    dsimp * at *,
    split,
    show ∀ (x : psum α β), (@co_zip φ ψ γ _ _ mc f₁ f₂).val (basis_sum ja jb x) = f x, {
      intros x; cases x with a b,
      case psum.inl {
        dunfold basis_sum,
        dunfold binary_module.zero,
        dunfold co_zip,
        dsimp [hom.comp,morphism.comp,function.comp],
        dsimp [has_add.add,binary_module.add],
        dsimp [premodel.act,vect.map],
        csimp only [vect.unzip_fam_eval,vect.map],
        dsimp [prod_fst,morphism.proj_fst],
        dsimp [prod_snd,morphism.proj_snd],
        rw [f₂.property],
        dunfold vect.map,
        let hz := @binary_module.add_zero γ mc,
        dsimp [binary_module.add, binary_module.zero] at hz,
        rw [hz],
        rw [hf₁.left]
      },
      case psum.inr {
        dunfold basis_sum,
        dunfold binary_module.zero,
        dunfold co_zip,
        dsimp [hom.comp,morphism.comp,function.comp],
        dsimp [has_add.add,binary_module.add],
        dsimp [premodel.act,vect.map],
        csimp only [vect.unzip_fam_eval,vect.map],
        dsimp [prod_fst,morphism.proj_fst],
        dsimp [prod_snd,morphism.proj_snd],
        rw [f₁.property],
        dunfold vect.map,
        let hz := @binary_module.zero_add γ mc,
        dsimp [binary_module.add, binary_module.zero] at hz,
        rw [hz],
        rw [hf₂.left]
      }
    },
    show ∀ (g : @hom (φ×ψ) γ _ mc), (∀ x, g.val (basis_sum ja jb x) = f x) → g = @co_zip φ ψ γ _ _ mc f₁ f₂, {
      intros g hg,
      apply subtype.eq,
      funext uv; cases uv with u v,
      rw [pair_is_sum (u,v)],
      dsimp [has_add.add,binary_module.add],
      rw [g.property],
      dsimp [vect.map],
      dunfold co_zip,
      dsimp [hom.comp,morphism.comp,function.comp],
      dsimp [has_add.add,binary_module.add],
      dsimp [premodel.act,vect.map,prod.map],
      rw [vect.unzip_fam_eval],
      rw [vect.unzip_fst_is_map_fst,vect.unzip_snd_is_map_snd],
      dsimp [vect.map],
      dsimp [prod_fst,morphism.proj_fst],
      dsimp [prod_inl,model.prod_inl],
      dsimp [prod_snd,morphism.proj_snd],
      dsimp [prod_inr,model.prod_inr],
      csimp only [fixed_elem_is_zero],
      let haz := @binary_module.add_zero φ _,
      let hza := @binary_module.zero_add ψ _,
      dsimp [binary_module.add,binary_module.zero] at haz hza,
      rw [haz,hza],
      suffices hgoal : (@hom.comp _ _ _ _ _ mc g prod_inl) = f₁ ∧ (@hom.comp _ _ _ _ _ mc g prod_inr) = f₂, {
        rw [←hgoal.left,←hgoal.right],
        refl
      },
      split,
      show (@hom.comp _ _ _ _ _ mc g prod_inl) = f₁, {
        apply hf₁.right _,
        intros a,
        exact hg (psum.inl a)
      },
      show (@hom.comp _ _ _ _ _ mc g prod_inr) = f₂, {
        apply hf₂.right _,
        intros b,
        exact hg (psum.inr b)
      }
    }
  end

#print axioms prod_free

end

end binary_module
