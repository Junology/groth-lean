
namespace subtype

--- `subtype.val` is injective
lemma val_injective {α : Type _} {p : α → Prop} : function.injective (@subtype.val α p) :=
  @subtype.eq α p

--- Relax the restriction on subtypes.
definition relax {α : Sort _} {p q : α → Prop} (f : ∀ a, p a → q a) : subtype p → subtype q :=
  λ x, subtype.cases_on x (λ a h, ⟨a, f a h⟩)

protected
definition inl {α : Sort _} {p q : α → Prop} : subtype p → subtype (λ a, p a ∨ q a) := relax (λ _, or.inl)

protected
definition inr {α : Sort _} {p q : α → Prop} : subtype q → subtype (λ a, p a ∨ q a) := relax (λ _, or.inr)

--- `relax` doesn't change the value.
lemma val_relax {α : Sort _} {p q : α → Prop} {f : ∀ a, p a → q a} : ∀ (x : subtype p), (x.relax f).val = x.val :=
  by intros x; cases x; refl

--- `inl` doesn't change the value.
lemma val_inl {α : Sort _} {p q : α → Prop} : ∀ (x : subtype p), (@subtype.inl _ p q x).val = x.val := λ x, by cases x; refl

--- `inr` doesn't change the value.
lemma val_inr {α : Sort _} {p q : α → Prop} : ∀ (x : subtype q), (@subtype.inr _ p q x).val = x.val := λ x, by cases x; refl

--- `relax` is injective function
lemma relax_inj {α : Type _} {p q : α → Prop} {f : ∀ a, p a → q a} : function.injective (relax f) :=
  begin
    intros x y,
    cases x; cases y; dunfold relax,
    dsimp *,
    exact subtype.eq ∘ congr_arg subtype.val
  end

--- Mapping into subtype yields a mapping into the underlying codomain all whose values belong to the subtype.
definition codomain {α β : Sort _} {p : β → Prop} (f : α → {b // p b}) : {f : α → β // ∀ a, p (f a)} :=
  ⟨subtype.val∘ f, λ a, (f a).property⟩

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
