
namespace subtype

--- Mapping into subtype yields a mapping into the underlying codomain all whose values belong to the subtype.
definition codomain {α β : Sort _} {p : β → Prop} (f : α → {b // p b}) : {f : α → β // ∀ a, p (f a)} :=
  ⟨subtype.val∘ f, λ a, (f a).property⟩

#print axioms subtype

--- If all the values of a mapping satisfy a predicator `p` on the codomain, it factors through the subtype defined by `p`.
definition factor_through {α β : Sort _} (f : α → β) (p : β → Prop) (h : ∀ a, p (f a)) : α → {b // p b} :=
  λ a, ⟨f a, h a⟩

theorem codomain_of_factor_through {α β : Sort _} (f : α → β) (p : β → Prop) (h : ∀ a, p (f a)) : ∀ a, (codomain (factor_through f p h)).val a = f a :=
  λ a, rfl

theorem factor_through_of_codomain {α : Sort _} {β : Type _} {p : β → Prop} (f : α → {b // p b}) : ∀ a, (factor_through (codomain f).val p (codomain f).property) a = f a :=
  begin
    intros,
    dsimp [codomain,function.comp,subtype.val],
    dunfold factor_through,
    exact subtype.eta (f a) _,
  end

end subtype