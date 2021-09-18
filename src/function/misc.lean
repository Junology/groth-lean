import logic.funrel

open function

namespace function

--- Dependent analogue of `curry`
definition dcurry {α : Sort _} {β : α → Sort _} {γ : Π a (b : β a), Sort _} (f : Π a (b : β a), γ a b) : Π (x : sigma β), γ x.fst x.snd :=
  λ x, f x.fst x.snd

--- Dependent analogue of `uncurry`
definition duncurry {α : Sort _} {β : α → Sort _} {γ : Π (x : sigma β), Sort _} (f : Π (x : sigma β), γ x) : Π a (b : β a), γ ⟨a,b⟩ :=
  λ a b, f ⟨a,b⟩

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

lemma bijective {α β : Sort _} {f : α → β} : has_inverse f → bijective f
| ⟨g, h⟩ := ⟨has_left_inverse.injective ⟨g, h.left⟩, has_right_inverse.surjective ⟨g, h.right⟩⟩

end has_inverse

--- Analogue of `congr` for functions with dependent domain.
definition dcongr {α : Sort _} {C : α → Sort _} {β : Sort _} : ∀ {a b : α} {f : C a → β} {g : C b → β} {x : C a} {y : C b}, a = b → f == g → x == y → f x = g y :=
  begin
    intros a b f g x y hab hfg hxy,
    cases hab,
    cases hfg,
    cases hxy,
    refl
  end

--- Analogue of `congr_arg` for functions with dependent codomain.
definition hcongr_arg {α : Sort _} {C : α → Sort _} (f : Π a, C a) : ∀ {x y : α}, x=y → f x == f y
| _ _ rfl := heq.rfl


end function
