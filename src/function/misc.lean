import logic.funrel

open function

namespace function

definition has_inverse {α β : Sort _} (f : α → β) : Prop :=
  ∃ (g : β → α), left_inverse g f ∧ right_inverse g f

theorem has_inverse_of_twosided_invertible {α β : Sort _} {f : α → β} : has_left_inverse f → has_right_inverse f → has_inverse f :=
  begin
    intros hlinv hrinv,
    cases hlinv with gl hgl,
    cases hrinv with gr hgr,
    existsi gl,
    split,
    show ∀ a, gl (f a) = a, { exact hgl },
    show ∀ b, f (gl b) = b, {
      intros b,
      by calc
        f (gl b)
            = f (gl (f (gr b))) : by rw [hgr]
        ... = f (gr b) : by rw [hgl]
        ... = b : hgr b
    }
  end

namespace has_inverse

lemma has_left_inverse {α β : Sort _} {f : α → β} : has_inverse f → function.has_left_inverse f :=
  begin
    intros hinv; cases hinv with g hg,
    exact ⟨g,hg.left⟩
  end

lemma has_right_inverse {α β : Sort _} {f : α → β} : has_inverse f → function.has_right_inverse f :=
  begin
    intros hinv; cases hinv with g hg,
    exact ⟨g,hg.right⟩
  end

#print axioms has_inverse.has_left_inverse
#print axioms has_inverse.has_right_inverse

lemma has_inverse.bijective {α β : Sort _} {f : α → β} : has_inverse f → bijective f :=
  begin
    intros hinv,
    split,
    show injective f, {
      exact function.has_left_inverse.injective hinv.has_left_inverse
    },
    show surjective f, {
      exact function.has_right_inverse.surjective hinv.has_right_inverse
    }
  end

end has_inverse


structure bijection (α β : Sort _) :=
  (f : α → β) (inv : β → α) (left_inverse : left_inverse inv f) (right_inverse : right_inverse inv f)

lemma bijection.f_has_inverse {α β : Sort _} (f : bijection α β) : has_inverse f.f :=
  begin
    existsi f.inv,
    split; try {exact f.left_inverse}; try {exact f.right_inverse}
  end

lemma bijection.inv_has_inverse {α β : Sort _} (f : bijection α β) : has_inverse f.inv :=
  begin
    existsi f.f,
    split; try {exact f.left_inverse}; try {exact f.right_inverse}
  end

namespace unsafe

noncomputable definition choose_inverse {α β : Sort _} (f : α → β) (hbij : bijective f) : bijection α β :=
{
  f := f,
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

end unsafe

end function
