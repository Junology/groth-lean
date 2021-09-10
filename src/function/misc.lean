import logic.funrel

open function

namespace function

--- Composition of retractions is again a retraction.
lemma left_inverse_comp {α β γ : Sort _} {gr : γ → β} {g : β → γ} {fr : β → α} {f : α → β} : left_inverse gr g → left_inverse fr f → left_inverse (fr∘ gr) (g∘f) :=
  begin
    intros hg hf a,
    dsimp [function.comp],
    rw [hg, hf]
  end

--- Composition of sections is again a section.
lemma right_inverse_comp {α β γ : Sort _} {gr : γ → β} {g : β → γ} {fr : β → α} {f : α → β} : right_inverse gr g → right_inverse fr f → right_inverse (fr∘ gr) (g∘f) :=
  λ hg hf, left_inverse_comp hf hg


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

end function
