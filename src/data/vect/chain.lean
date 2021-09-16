import data.vect.basic
import tactic.csimp

universe u

--- Check whether a given vector is monotonic with respect to a given binary relation.
definition is_monotonic {α : Type*} (r : α → α → Prop) : ∀ {n : ℕ}, vect α n → Prop
| _ vect.nil := true
| _ (vect.cons _ vect.nil) := true
| _ (vect.cons x (vect.cons y ys)) := r x y ∧ is_monotonic (vect.cons y ys)

inductive based_chain {α : Type u} (r : α → α → Prop) : α → ℕ → Type u
| base (x : α) : based_chain x 1
| cons {n : ℕ} (x : α) {y : α} (_ : r x y) (xs : based_chain y n) : based_chain x (n+1)

namespace based_chain

definition to_vect {α : Type*} {r : α → α → Prop} : Π {x : α} {n : ℕ}, based_chain r x n → vect α n
| x _ (base _) := vect.cons x vect.nil
| x _ (cons _ h xs) := vect.cons x (to_vect xs)

lemma to_vect_is_monotonic {α : Type*} {r : α → α → Prop} : Π {x : α} {n : ℕ} (ch : based_chain r x n), is_monotonic r ch.to_vect
| _ _ (base x) := by csimp [to_vect,is_monotonic]
| _ _ (cons x h (base y)) := by csimp [to_vect,is_monotonic]; exact ⟨h,true.intro⟩
| _ _ (cons x hxy (cons y h ch)) :=
  begin
    have h_ind : is_monotonic r (cons y h ch).to_vect,
      from to_vect_is_monotonic (cons y h ch),
    csimp [to_vect,is_monotonic] at *,
    split,
    show r x y, from hxy,
    show is_monotonic r (vect.cons y ch.to_vect), from h_ind
  end

definition from_vect {α : Type*} {r : α → α → Prop} : Π {n : ℕ} (xs : vect α (n+1)) (hmono : is_monotonic r xs), based_chain r xs.head (n+1)
| _ (vect.cons x vect.nil) hmono := based_chain.base x
| n (vect.cons x (vect.cons y ys)) hmono :=
  let tail := from_vect (vect.cons y ys) hmono.right
  in cons x hmono.left tail

definition from_vect' {α : Type*} {r : α → α → Prop} {n : ℕ} (xs : vect α (n+1)) (hmono : is_monotonic r xs) : Σ x, based_chain r x (n+1) :=
  ⟨xs.head, from_vect xs hmono⟩

lemma tail_heq {α : Type _} {r : α → α → Prop} (x : α) {n : ℕ} : Π {y₁ y₂ : α} (hxy₁ : r x y₁) (hxy₂ : r x y₂) {ys₁ : based_chain r y₁ n} {ys₂ : based_chain r y₂ n}, (y₁ = y₂) → ys₁ == ys₂ → cons x hxy₁ ys₁ = cons x hxy₂ ys₂ :=
  begin
    intros _ _ _ _ _ _ hy hys,
    cases hy, cases hy,
    have : ys₁ = ys₂ := eq_of_heq hys,
    rw [this]
  end

lemma to_vect_of_from {α : Type*} {r : α → α → Prop} : Π {n : ℕ} (xs : vect α (n+1)) (hmono : is_monotonic r xs), (from_vect xs hmono).to_vect = xs
| _ (vect.cons x vect.nil) hmono := by dsimp [from_vect,to_vect,vect.head]; refl
| _ (vect.cons x (vect.cons y ys)) hmono :=
  begin
    dsimp only [from_vect,to_vect],
    unfold vect.head,
    let h_ind := to_vect_of_from (vect.cons y ys) hmono.right,
    rw [h_ind]
  end

attribute [simp,reducible]
lemma head_of_to_vect {α : Type*} {r : α → α → Prop} : Π {x : α} {n : ℕ} (ch : based_chain r x (n+1)), ch.to_vect.head = x
| _ _ (base x) := rfl
| _ _ (cons x h ys) := rfl

lemma from_vect_of_to {α : Type*} {r : α → α → Prop} : Π {x : α} {n : ℕ} (ch : based_chain r x (n+1)), (from_vect' ch.to_vect (to_vect_is_monotonic ch)) = ⟨x,ch⟩
| _ _ (base x) := rfl
| _ _ (cons x h (base y)) := rfl
| _ _ (cons x hxy (cons y h ys)) :=
  begin
    let h_ind := from_vect_of_to (cons y h ys),
    unfold to_vect at *,
    unfold from_vect' at *,
    apply sigma.eq; try {unfold sigma.fst at *}; try {unfold sigma.snd at *},
    dsimp [from_vect],
    refine tail_heq x _ hxy _ _; try {refl},
    exact (sigma.mk.inj h_ind).right
  end

end based_chain
