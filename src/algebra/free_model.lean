import algebra.theory

definition is_free {th : theory} {α β : Type _} [mb : model th β] (j : α → β) : Prop :=
  ∀ {γ : Type _} [mc : model th γ] (f : α → γ), ∃! (g : @morphism th β γ mb.to_premodel mc.to_premodel), ∀ (a : α), @morphism.to_fun th β γ mb.to_premodel mc.to_premodel g (j a) = f a


-- TO DO: define the free algebraic model using optree
