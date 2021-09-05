import algebra.optree
import data.vect.basic
import data.finite.finord

universes u v

-- Structure for algebraic theories
structure theory :=
  mk :: (op : ℕ → Type) (rel : ℕ → Type)
        (rel_lhs : ∀ {n : ℕ}, rel n → optree op (finord n))
        (rel_rhs : ∀ {n : ℕ}, rel n → optree op (finord n))


-- Pre-model of a theory; i.e. sets with structure maps which not necessarily satisfy the axioms.
class premodel (th : theory) (α : Type u) : Type u :=
  mk :: (act : Π {n : ℕ}, th.op n → vect α n → α)

-- Model of a theory
class model (th : theory) (α : Type u) extends premodel th α : Type u:=
  mk :: (haxiom : ∀ {n : ℕ} (r : th.rel n) (var : finord n → α), (th.rel_lhs r).elim @act var = (th.rel_rhs r).elim @act var)

instance model_is_premodel(th : theory) (α : Type _) [ha : model th α] : premodel th α := ha.to_premodel


namespace premodel

definition action (th : theory) (α : Type _) [premodel th α] : Π {n : ℕ}, th.op n → vect α n → α := @premodel.act th α _

end premodel


namespace model

definition axiom_eq (th : theory) (α : Type _) [model th α] : ∀ {n : ℕ} (r : th.rel n) (var : finord n → α), (th.rel_lhs r).elim (@premodel.act th α _) var = (th.rel_rhs r).elim (@premodel.act th α _) var := @model.haxiom th α _

--- Trivial model; `unit` is always a model of any algebraic theory.
instance triv (th : theory) : model th unit :=
{
  act := λ _ _ _, (),
  haxiom :=
    begin
      intros,
      dsimp [premodel.act],
      have : ∀ {x y: unit}, x=y,
        by intros  x y; cases x; cases y; refl,
      exact this
    end
}

#print axioms model.triv

end model


/-*****************************
 - Morphisms of pre-models
 -*****************************-/

@[reducible]
definition is_morphism (th : theory) {α : Type u} {β : Type v} [premodel th α] [premodel th β] (f : α → β) : Prop := ∀ {n : ℕ} (μ : th.op n) (as : vect α n), f (@premodel.act th α _ _ μ as) = (@premodel.act th β _ _ μ (as.map f))

structure morphism (th : theory) (α : Type u) (β : Type v) [premodel th α] [premodel th β] : Type.{max u v+1}:=
  mk :: (to_fun : α → β) (hact : is_morphism th to_fun)

namespace morphism

protected
definition coe_to_fun {th : theory} (α : Type _) (β : Type _) [premodel th α] [premodel th β] : has_coe_to_fun (morphism th α β)  :=
  {
    F := λ_, α → β,
    coe := morphism.to_fun
  }

attribute [instance] morphism.coe_to_fun

-- the identity morphism
definition id {th : theory} {α : Type _} [premodel th α] : morphism th α α :=
  {
    to_fun := id,
    hact := by intros n u as; rw [vect.map_id]; refl
  }

-- the composition of morphisms
definition comp {th : theory} {α β γ : Type _} [premodel th α] [premodel th β] [premodel th γ] : morphism th β γ → morphism th α β → morphism th α γ :=
  λ g f,
    {
      to_fun := g.to_fun ∘ f.to_fun,
      hact :=
        begin
          intros n k cs,
          unfold function.comp,
          rw [vect.map_comp],
          rw [f.hact,g.hact]
        end
    }

#print axioms morphism.comp

-- Two morphisms equal to each other as soon as their underlying maps do
theorem morphism_eq {th : theory} {α β : Type _} [premodel th α] [premodel th β] {f g : morphism th α β} : f.to_fun = g.to_fun → f = g :=
  begin
    intros h,
    cases f,
    cases g,
    unfold morphism.to_fun at h,
    cases h,
    refl
  end

#print axioms morphism_eq

-- The image of every morphism is closed under operations
theorem image_act {th : theory} {α β : Type _} [premodel th α] [premodel th β] (f : morphism th α β) : ∀ {n : ℕ} {k : th.op n} {ys : vect {b // ∃ a, f.to_fun a = b} n}, ∃ a, f.to_fun a = (@premodel.act th β _ _ k) (vect.map subtype.val ys) :=
  begin
    intros,
    apply exists.elim (vect.image ys),
    intros as has,
    existsi (@premodel.act th α _ _ k) as,
    rw [f.hact, has]
  end

#print axioms image_act

-- The image of a morphism forms a premodel
definition image_premodel {th : theory} {α β : Type _} [premodel th α] [premodel th β] (f : morphism th α β) : premodel th {b // ∃ a, f.to_fun a = b} :=
  {
    act :=
      λ n k xs, ⟨@premodel.act th β _ _ k (vect.map subtype.val xs), image_act f⟩
  }

-- The image of a morphism in a model forms a model
definition image_model {th : theory} {α β : Type _} [premodel th α] [model th β] (f : morphism th α β) : model th {b // ∃ a, f.to_fun a = b} :=
  {
    to_premodel := image_premodel f,
    haxiom :=
      begin
        intros,
        dsimp [image_premodel] at *,
        apply subtype.eq,
        rw [optree.elim_subtype,optree.elim_subtype],
        rw [model.axiom_eq]
      end
  }

#print axioms image_model

end morphism