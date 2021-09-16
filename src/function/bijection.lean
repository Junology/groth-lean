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

#print axioms to_bijection

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
