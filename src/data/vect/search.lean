import .basic

namespace vect

definition is_all {α : Type _} (p : α → Prop) : ∀ {n : ℕ}, vect α n → Prop
| _ vect.nil := true
| _ (vect.cons a as) := p a ∧ is_all as

definition is_any {α : Type _} (p : α → Prop) : ∀ {n : ℕ}, vect α n → Prop
| _ vect.nil := false
| _ (vect.cons a as) := p a ∨ is_any as

theorem map_all {α β : Type _} {f : α → β} (p : β → Prop) (hpf : ∀ a, p (f a)) : ∀ {n : ℕ} {v : vect α n}, is_all p (vect.map f v)
| _ vect.nil := true.intro
| _ (vect.cons a as) := ⟨hpf a, map_all⟩

definition is_diagonal {α : Type _} (a : α) : ∀ {n : ℕ}, vect α n → Prop := @is_all α (λ b, a=b)

theorem is_diagonal_eq_repeat {α : Type _} (a : α) : ∀ {n : ℕ} {as : vect α n}, is_diagonal a as → as = repeat a n
| _ vect.nil _ := rfl
| (n+1) (vect.cons a' as) hdiag :=
  begin
    dsimp [repeat];
    rw [←hdiag.left, is_diagonal_eq_repeat hdiag.right],
  end

end vect
