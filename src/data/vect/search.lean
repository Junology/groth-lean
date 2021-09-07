import .basic

namespace vect

definition is_all {α : Type _} (p : α → Prop) : ∀ {n : ℕ}, vect α n → Prop
| _ ⁅⁆ := true
| _ (a ∺ as) := p a ∧ is_all as

definition is_any {α : Type _} (p : α → Prop) : ∀ {n : ℕ}, vect α n → Prop
| _ ⁅⁆ := false
| _ (a ∺ as) := p a ∨ is_any as

--- All entries of `vect` of sybtype `subtype p` satisfy `p`
theorem is_all_subtype {α : Type _} {p : α → Prop} : ∀ {n} {xs : vect {a//p a} n}, is_all p (xs.map subtype.val)
| _ ⁅⁆ := true.intro
| _ (x ∺ xs) := ⟨x.property, is_all_subtype⟩

--- If all mapped values of `f` satisfy `p`, then all entries of `map f` of a vector satisfy `p`.
theorem map_all {α β : Type _} {f : α → β} (p : β → Prop) (hpf : ∀ a, p (f a)) : ∀ {n : ℕ} {v : vect α n}, is_all p (vect.map f v)
| _ ⁅⁆ := true.intro
| _ (a ∺ as) := ⟨hpf a, map_all⟩

--- Assertion that a given vector consists of a unique element.
definition is_diagonal {α : Type _} (a : α) : ∀ {n : ℕ}, vect α n → Prop := @is_all α (λ b, a=b)

theorem is_diagonal_eq_repeat {α : Type _} (a : α) : ∀ {n : ℕ} {as : vect α n}, is_diagonal a as → as = repeat a n
| _ ⁅⁆ _ := rfl
| (n+1) (a' ∺ as) hdiag :=
  begin
    dsimp [repeat];
    rw [←hdiag.left, is_diagonal_eq_repeat hdiag.right],
  end

end vect
