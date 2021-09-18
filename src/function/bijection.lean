import .misc

open function

--- A structure that carries a map together with a specified inverse.
structure bijection (α β : Sort _) :=
  (to_fun : α → β) (inv : β → α) (left_inverse : left_inverse inv to_fun) (right_inverse : right_inverse inv to_fun)

@[reducible,inline]
instance bijection_to_fun (α β : Sort _) : has_coe_to_fun (bijection α β) :=
{
  F := _,
  coe := bijection.to_fun
}

namespace bijection

--- The underlying map of `bijection α β` has an inverse.
protected
lemma has_inverse {α β : Sort _} (f : bijection α β) : has_inverse f.to_fun :=
  ⟨f.inv, ⟨f.left_inverse, f.right_inverse⟩⟩

--- The inverse part of `bijection α β` has an inverse.
protected
lemma inv_has_inverse {α β : Sort _} (f : bijection α β) : has_inverse f.inv :=
  ⟨f.to_fun, ⟨f.right_inverse, f.left_inverse⟩⟩

--- Bijections are injective.
protected
lemma is_injective {α β : Sort _} (f : bijection α β) : injective f.to_fun :=
  has_left_inverse.injective ⟨f.inv, f.left_inverse⟩

--- Bijections are surjective.
protected
lemma is_surjective {α β : Sort _} (f : bijection α β) : surjective f.to_fun :=
  has_right_inverse.surjective ⟨f.inv, f.right_inverse⟩

--- Bijections are bijective.
protected
lemma is_bijective {α β : Sort _} (f : bijection α β) : bijective f.to_fun :=
  ⟨f.is_injective, f.is_surjective⟩

--- The inverses of bijections are injective.
protected
lemma inv_is_injective {α β : Sort _} (f : bijection α β) : injective f.inv :=
  has_left_inverse.injective ⟨f.to_fun, f.right_inverse⟩

--- The inverses of bijections are surjective.
protected
lemma inv_is_surjective {α β : Sort _} (f : bijection α β) : surjective f.inv :=
  has_right_inverse.surjective ⟨f.to_fun, f.left_inverse⟩

--- The inverses of bijections are bijective
protected
lemma inv_is_bijective {α β : Sort _} (f : bijection α β) : bijective f.inv :=
  ⟨f.inv_is_injective, f.inv_is_surjective⟩

--- The identity if a bijection
protected
definition id {α : Sort _} : bijection α α :=
{
  to_fun := @id α,
  inv := @id α,
  left_inverse := λ _, rfl,
  right_inverse := λ _, rfl
}

--- The composition of bijections is a bijection.
protected
definition comp {α β γ : Sort _} (g : bijection β γ) (f : bijection α β) : bijection α γ :=
{
  to_fun := g.to_fun ∘ f.to_fun,
  inv := f.inv ∘ g.inv,
  left_inverse := left_inverse_comp g.left_inverse f.left_inverse,
  right_inverse := right_inverse_comp g.right_inverse f.right_inverse
}

--- Bijections are invertible.
protected
definition inverse {α β : Sort _} (f : bijection α β) : bijection β α :=
{
  to_fun := f.inv,
  inv := f.to_fun,
  left_inverse := f.right_inverse,
  right_inverse := f.left_inverse
}

--- The subtype `{a : α // true}` is isomorphic to `α` itself.
definition subtype_true (α : Sort _) : bijection {x : α // true} α :=
{
  to_fun := subtype.val,
  inv := λ x, ⟨x, true.intro⟩,
  left_inverse := λ x, by cases x; refl,
  right_inverse := @rfl α
}

--- The subtypes classified by equivalent propositions are isomorphic.
definition subtype_equiv {α : Sort _} {p q : α → Prop} (hpq: ∀ x, p x ↔ q x) : bijection (subtype p) (subtype q) :=
{
  to_fun := λ x, subtype.rec_on x (λ a h, ⟨a, iff.mp (hpq a) h⟩),
  inv := λ x, subtype.rec_on x (λ a h, ⟨a, iff.mpr (hpq a) h⟩),
  left_inverse := λ x, by cases x; refl,
  right_inverse := λ x, by cases x; refl
}

--- Subtypes of a subtype is just a subtype of the root type.
definition subtype_uncurry {α : Sort _} {p q : α → Prop} : bijection {x : subtype p // q x.val} {x : α // p x ∧ q x} :=
{
  to_fun := λ x, ⟨x.val.val, ⟨x.val.property, x.property⟩⟩,
  inv := λ x, ⟨⟨x.val,x.property.left⟩,x.property.right⟩,
  left_inverse := λ x, by cases x; cases x_val; refl,
  right_inverse := λ x, by cases x; refl
}

--- Subtypes of a subtype is just a subtype of the root type.
definition subtype_curry {α : Sort _} {p q : α → Prop} : bijection {x : α // p x ∧ q x} {x : subtype p // q x.val} :=
{
  to_fun := λ x, ⟨⟨x.val,x.property.left⟩,x.property.right⟩,
  inv := λ x, ⟨x.val.val, ⟨x.val.property, x.property⟩⟩,
  left_inverse := λ x, by cases x; refl,
  right_inverse := λ x, by cases x; cases x_val; refl
}

/- In the following, we use `funext` and `definite_description`. -/
namespace unsafe

--- Construct an term of `bijection α β` from a bijective map by choosing its inverse.
noncomputable definition to_bijection {α β : Sort _} (f : α → β) (hbij : bijective f) : bijection α β :=
{
  to_fun := f,
  inv := funrel.unsafe.reify (funrel.inverse_of_bijective hbij),
  left_inverse :=
    begin
      intros a,
      rw [←funrel.unsafe.reify_fun_id f],
      exact (funrel.unsafe.reify_inverse (funrel.bijective_fun_isom hbij)).left a,
    end,
  right_inverse :=
    begin
      intros b,
      rw [←funrel.unsafe.reify_fun_id f],
      exact (funrel.unsafe.reify_inverse (funrel.bijective_fun_isom hbij)).right b
    end
}

--- `subsingleton` type is isomorphic to a `nonempty` proposition
noncomputable definition subsingleton_is_proposition (α : Sort _) [subsingleton α] : bijection α (nonempty α) :=
  to_bijection (@nonempty.intro α) $
    begin
      split,
      show injective _,
        by intros a b _; exact subsingleton.elim a b,
      show surjective _,
        by intros h; exact h.elim (λ a, exists.intro a rfl)
    end

end unsafe

end bijection
