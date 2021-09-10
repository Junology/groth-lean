import .misc

open function

--- A structure that carries a map together with a specified inverse.
structure bijection (α β : Sort _) :=
  (to_fun : α → β) (inv : β → α) (left_inverse : left_inverse inv to_fun) (right_inverse : right_inverse inv to_fun)


namespace bijection

lemma f_has_inverse {α β : Sort _} (f : bijection α β) : has_inverse f.to_fun :=
  begin
    existsi f.inv,
    split; try {exact f.left_inverse}; try {exact f.right_inverse}
  end

lemma inv_has_inverse {α β : Sort _} (f : bijection α β) : has_inverse f.inv :=
  begin
    existsi f.to_fun,
    split; try {exact f.left_inverse}; try {exact f.right_inverse}
  end

protected
definition comp {α β γ : Sort _} (g : bijection β γ) (f : bijection α β) : bijection α γ :=
{
  to_fun := g.to_fun ∘ f.to_fun,
  inv := f.inv ∘ g.inv,
  left_inverse := left_inverse_comp g.left_inverse f.left_inverse,
  right_inverse := right_inverse_comp g.right_inverse f.right_inverse
}

namespace unsafe

--- Construct an term of `bijection α β` from a bijective map by choosing its inverse.
noncomputable definition choose_inverse {α β : Sort _} (f : α → β) (hbij : bijective f) : bijection α β :=
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

#print axioms choose_inverse

--- `subsingleton` type is isomorphic to a `nonempty` proposition
noncomputable definition subsingleton_is_proposition (α : Sort _) [subsingleton α] : bijection α (nonempty α) :=
  choose_inverse (@nonempty.intro α) $
    begin
      split,
      show injective _,
        by intros a b _; exact subsingleton.elim a b,
      show surjective _,
        by intros h; exact h.elim (λ a, exists.intro a rfl)
    end

end unsafe

end bijection
