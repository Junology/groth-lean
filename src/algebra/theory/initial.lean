import data.vect
import .basic .prod

/-!
 * Theories that have trivial initial models.
-/

namespace model

--- `is_initial th α` guarantees that `α` is an initial model of the theory `th`.
structure is_initial (th : theory) (α : Type _) [model th α] :=
  (elim : Π {β : Type _} [mb : model th β], @morphism th α β _ mb.to_premodel)
  (hunique : Π {β : Type _} [mb : model th β], ∀ (g : @morphism th α β _ mb.to_premodel) (a : α), g.val a = elim.val a)

--- `has_trivial_init th` can be defined if `unit` is an initial model of the theory `th`. Examples include groups and abelian groups. Non-examples include unital rings.
class has_trivial_init (th : theory) :=
  (init_unit : is_initial th unit)

--- If a theory `th` has `unit` as an initial model, then every model of `th` admits an element that is closed under operations in the theory.
definition fixed_element (th : theory) [ht : has_trivial_init th] (α : Type _) [model th α] : α := ((@is_initial.elim th unit _ ht.init_unit) α _).val ()

--- Proof that `fixed th α` is closed under operations in the theory `th`.
theorem fixed_op (th : theory) [ht : has_trivial_init th] (α : Type _) [model th α] : ∀ {n} μ, fixed_element th α = @premodel.act th α _ n μ (vect.repeat (fixed_element th α) n) :=
  begin
    intros n μ,
    dsimp [fixed_element],
    cases hht: ht.init_unit with f hf,
    dsimp [is_initial.elim],
    rw [←vect.map_repeat],
    let hact := (@f α _).property,
    dunfold is_morphism at hact,
    rw [←hact],
    dsimp [premodel.act],
    refl
  end

#print axioms fixed_op

theorem fixed_const (th : theory) [ht : has_trivial_init th] (α : Type _) [model th α] : ∀ (μ : th.op 0), fixed_element th α = @premodel.act th α _ _ μ vect.nil :=
  fixed_op th α

--- The morphism that factors through the terminal model.
definition null_morphism (th : theory) [ht : has_trivial_init th] (α β : Type _) [model th α] [model th β] : morphism th α β :=
  ⟨(λ _, fixed_element th β), by intros n μ as; dsimp *; rw [vect.map_const,←fixed_op th β μ]⟩

--- If `unit` is an initial model, then there is a canonical morphism that injects a model `α` into the first component of a product `α×β`.
definition prod_inl (th : theory) [has_trivial_init th] {α β : Type _} [model th α] [model th β] : morphism th α (α×β) :=
{
  val := λ a, (a, fixed_element th β),
  property :=
    begin
      intros n μ as,
      dsimp [premodel.act, prod.map],
      rw [vect.unzip_fst_is_map_fst, vect.unzip_snd_is_map_snd],
      csimp [←vect.map_comp],
      dsimp [function.comp],
      have : @id α = (λ x,x) , from rfl,
      rw [←this,vect.map_id]; clear this,
      rw [vect.map_const],
      rw [←fixed_op th β μ],
    end
}

--- If `unit` is an initial model, then there is a canonical morphism that injects a model `β` into the second component of a product `α×β`.
definition prod_inr (th : theory) [has_trivial_init th] {α β : Type _} [model th α] [model th β] : morphism th β (α×β) :=
{
  val := λ b, (fixed_element th α,b),
  property :=
    begin
      intros n μ as,
      dsimp [premodel.act, prod.map],
      rw [vect.unzip_fst_is_map_fst, vect.unzip_snd_is_map_snd],
      csimp [←vect.map_comp],
      dsimp [function.comp],
      have : @id β = (λ x,x) , from rfl,
      rw [←this,vect.map_id]; clear this,
      rw [vect.map_const],
      rw [←fixed_op th α μ],
    end
}

#print axioms prod_inl
#print axioms prod_inr

end model
