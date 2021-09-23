import .basic

/-!
 * Hom group of binary_modules.
 -/

namespace binary_module

local attribute [instance] has_binary_add

--- The predicator `is_morphism` is invariant in the type `α → β` under the pointwise operations of binary_modules.
definition inv_is_morphism (α β : Type _) [model binary_module α] [model binary_module β] : inv_pred binary_module (α → β) :=
{
  p := is_morphism binary_module,
  hinv :=
    begin
      intros _ μ fs hfs,
      dunfold is_morphism,
      cases μ,
      case ops.zero {
        cases fs,
        intros _ μ as,
        dunfold premodel.act,
        dsimp *,
        dsimp [vect.unzip_fam],
        rw [vect.map_const],
        let hfix := @model.fixed_op binary_module binary_module.has_trivial_init β _,
        dsimp [model.fixed_element,model.has_trivial_init.init_unit,unit_is_initial,morphism.zero,binary_module.zero] at hfix,
        rw [←hfix]
      },
      case ops.add {
        cases fs with _ f fs, cases fs with _ g gs, cases gs,
        dunfold vect.is_all at hfs,
        unfold premodel.act,
        intros _ μ as,
        dsimp *,
        cases μ,
        case ops.zero {
          cases as,
          rw [vect.unzip_fam_eval],
          dsimp [vect.map],
          rw [hfs.left,hfs.right.left],
          dsimp [vect.map],
          exact binary_module.add_self _
        },
        case ops.add {
          cases as with _ a as; cases as with _ b bs; cases bs,
          dsimp [vect.map],
          repeat {rw [vect.unzip_fam_eval]},
          dsimp [vect.map],
          rw [hfs.left,hfs.right.left]; dsimp [vect.map],
          let hassoc := @binary_module.add_assoc β _,
          let hcomm := @binary_module.add_comm β _,
          dsimp [binary_module.add] at hassoc hcomm,
          rw [hassoc (f a) (f b) _, ←hassoc (f b) (g a) (g b)],
          rw [hcomm (f b) (g a)],
          repeat { rw [hassoc] }
        }
      }
    end
}

#print axioms inv_is_morphism

--- The hom-set between binary_modules forms a binary_module.
@[reducible,inline]
definition hom (α β : Type _) [model binary_module α] [model binary_module β] := submodel binary_module (inv_is_morphism α β)

namespace hom

--- Composition of homomorphisms.
@[reducible,inline]
protected
definition comp {α β γ: Type _} [model binary_module α] [model binary_module β] [model binary_module γ] : hom β γ → hom α β → hom α γ := morphism.comp

--- Evaluation at `a : α` defines a homomorphism from `hom α β` to `β`.
@[reducible]
protected
definition eval (α β : Type _) [model binary_module α] [model binary_module β] (a : α) : morphism binary_module (hom α β) β :=
{
  val := λ f, f.val a,
  property :=
    begin
      intros _ μ fs,
      dsimp *,
      let hj := (@submodel.sub_incl binary_module (α → β) _ (inv_is_morphism α β)).property,
      unfold is_morphism at hj,
      dsimp [submodel.sub_incl] at hj,
      rw [hj],
      unfold premodel.act,
      rw [vect.unzip_fam_eval,←vect.map_comp]
    end
}

#print axioms hom.eval

--- For every pair of `binary_module`s `α` and `β`, the type of homomorphisms `hom α β` is point-wisely a model of `binary_module`; i.e. up to `funext`.
definition is_model_ptwise (α β : Type _) [model binary_module α] [model binary_module β] : ∀ {n : ℕ} (r : binary_module.rel n) (var : finord n → hom α β) (a : α), ((binary_module.rel_lhs r).elim (@premodel.act binary_module (hom α β) _) var).val a = ((binary_module.rel_rhs r).elim (@premodel.act binary_module (hom α β) _) var).val a :=
  begin
    intros n r var a,
    let hp := @optree.elim_funap binary_module.ops (finord n) (hom α β) β (@premodel.act binary_module (hom α β) _) (@premodel.act binary_module β _) var (hom.eval α β a).val (hom.eval α β a).property,
    delta hom.eval at hp,
    dsimp [subtype.val,function.comp] at hp,
    rw [hp,hp],
    rw [model.axiom_eq],
  end

#print axioms hom.is_model_ptwise

namespace unsafe

--- For every pair of `binary_module`s `α` and `β`, the type of homomorphisms `hom α β` is a model of `binary_module`.
definition is_model (α β : Type _) [model binary_module α] [model binary_module β] : model binary_module (hom α β) :=
{
  haxiom := λ _ r var, subtype.eq (funext (@is_model_ptwise α β _ _ _ r var))
}

#print axioms hom.unsafe.is_model

end unsafe

section

local infixl `●`:100 := hom.comp
local attribute [instance] binary_module.has_binary_add

--- Composition is linear in the right operand.
theorem comp_bilinear_right_ptwise (α β γ: Type _) [model binary_module α] [model binary_module β] [model binary_module γ] (g : hom β γ) (f₁ f₂ : hom α β) : ∀ (a : α), (g ● (f₁+ f₂)).val a = ((g ● f₁) + (g ● f₂)).val a :=
  begin
    intros a,
    dsimp [has_add.add,binary_module.add,hom.comp,morphism.comp],
    dsimp [premodel.act,vect.map,subtype.val],
    csimp only [vect.unzip_fam_eval,vect.map],
    rw [g.property],
    dsimp [vect.map,function.comp],
    refl
  end

#print axioms comp_bilinear_right_ptwise

--- Composition is linear in the left operand.
theorem comp_bilinear_left_ptwise (α β γ: Type _) [model binary_module α] [model binary_module β] [model binary_module γ] (g₁ g₂ : hom β γ) (f : hom α β) : ∀ (a : α), ((g₁+g₂) ● f).val a = ((g₁ ● f) + (g₂ ● f)).val a :=
  begin
    intros a,
    dsimp [has_add.add,binary_module.add,hom.comp,morphism.comp],
    dsimp [premodel.act,vect.map,subtype.val],
    csimp only [vect.unzip_fam_eval,vect.map],
  end

#print axioms comp_bilinear_left_ptwise

end

end hom

end binary_module
