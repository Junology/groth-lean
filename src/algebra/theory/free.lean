import .basic
import function.misc function.bijection

universe u

@[reducible]
definition is_free (th : theory) {α : Sort _} {β : Type _} [mb : model th β] (j : α → β) : Prop :=
  ∀ {γ : Type u} [mc : model th γ] (f : α → γ), ∃! (g : @morphism th β γ mb.to_premodel mc.to_premodel), ∀ (a : α), g.val (j a) = f a

lemma free_on_bijective_bases (th : theory) {α β : Sort _} {φ : Type _} [mb : model th φ] (u : bijection α β) (j : β → φ) : is_free.{u} th j → is_free.{u} th (j∘ u.to_fun) :=
  begin
    intros hfree,
    intros ψ mpsi g,
    cases @hfree ψ mpsi (g∘ u.inv) with g₁ hg₁,
    existsi g₁,
    dsimp [function.comp] at *,
    split,
    show ∀ (a : α), g₁.val (j (u.to_fun a)) = g a, {
      intros a,
      by calc
        g₁.val (j (u.to_fun a))
            = g (u.inv (u.to_fun a)) : hg₁.left (u.to_fun a)
        ... = g a : by rw [u.left_inverse a]
    },
    show ∀ (g' : @morphism th φ ψ _ mpsi.to_premodel), (∀ a, g'.val (j (u.to_fun a)) = g a) → g' = g₁, {
      intros g' hg',
      apply hg₁.right g',
      intros b,
      by calc
        g'.val (j b)
            = g'.val (j (u.to_fun (u.inv b))) : by rw [u.right_inverse b]
        ... = g (u.inv b) : hg' (u.inv b)
    }
  end

#print axioms free_on_bijective_bases

-- TO DO: define the free algebraic model using optree

