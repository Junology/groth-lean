import data.list.misc

@[algebra]
class has_add_abelian (α : Sort _) extends has_add α, has_zero α, has_neg α :=
  (add_zero : ∀ (x : α), x + 0 = x)
  (add_comm : ∀ (x y : α), x + y = y + x)
  (add_assoc : ∀ (x y z : α), (x + y) + z = x + (y + z))
  (add_neg : ∀ (x : α), x + (-x) = 0)

instance has_add_abelian_sub (α : Sort _) [has_add_abelian α] : has_sub α :=
  has_sub.mk (λ x y, x + (-y))


section

universe u
variables {α : Type u} [has_add_abelian α]

@[simp]
lemma add_zero : ∀ (x : α), x + 0 = x := has_add_abelian.add_zero

@[simp]
lemma zero_add : ∀ (x : α), 0 + x = x :=
  λ x, eq.trans (has_add_abelian.add_comm 0 x) (add_zero _)

lemma add_comm : ∀ (x y : α), x + y = y + x :=
  has_add_abelian.add_comm

lemma add_assoc : ∀ (x y z : α), (x + y) + z = x + (y + z) :=
  has_add_abelian.add_assoc

@[simp]
lemma add_neg : ∀ (x : α), x + (-x) = 0 :=
  has_add_abelian.add_neg

@[simp]
lemma neg_add : ∀ (x : α), (-x) + x = 0 :=
  λ x, eq.trans (add_comm (-x) x) (add_neg x)

@[simp]
lemma sub_self : ∀ (x : α), x - x = 0 := add_neg

@[simp]
lemma sub_neg : ∀ (x : α), 0 - x = -x := λ x, zero_add (-x)

end

@[reducible]
definition accum {α β: Sort _} [has_add_abelian β] (f : α → β) : list α → β :=
  λ l, l.foldr (λ a b, f a + b) 0

section

variables {α β : Type _} [has_add_abelian β] {f : α → β}

@[simp]
lemma accum_nil : accum f [] = 0 := rfl

@[simp]
lemma accum_cons {a : α} {as : list α} : accum f (a::as) = f a + accum f as := rfl

@[simp]
lemma accum_zero : (∀ a, f a = 0) → ∀ (as : list α), accum f as = 0
| _ [] := rfl
| h (a::as) :=
  by calc
    accum f (a::as)
        = f a + accum f as : rfl
    ... = f a + 0 : by rw [accum_zero h as]
    ... = f a : add_zero (f a)
    ... = 0 : h a

@[simp]
lemma accum_append (l₁ l₂ : list α) : accum f (l₁ ++ l₂) = accum f l₁ + accum f l₂ :=
  begin
    induction l₁ with a tl h_ind,
    case nil {
      rw [list.nil_append, accum_nil, zero_add],
    },
    case cons {
      dsimp [list.append],
      rw [h_ind, add_assoc],
    }
  end

lemma accum_filter_zero {p : α → Prop} [decidable_pred p] : (∀ x, ¬p x → f x = 0) → ∀ (l : list α), accum f (l.filter p) = accum f l
| _ [] := rfl
| h (a::as) :=
  dite (p a)
    /- p a -/ (
      λ hpa, calc
        accum f (list.filter p (a :: as))
            = accum f (a :: as.filter p) : by rw [as.filter_cons_of_pos hpa]
        ... = f a + accum f (as.filter p) : rfl
        ... = f a + accum f as : by rw [accum_filter_zero h as]
        ... = accum f (a :: as) : rfl
    )
    /- ¬p a -/ (
      λ hnpa, calc
        accum f (list.filter p (a :: as))
            = accum f (as.filter p) : by rw [as.filter_cons_of_neg hnpa]
        ... = accum f as : by rw [←accum_filter_zero h as]
        ... = 0 + accum f as : by rw [zero_add]
        ... = f a + accum f as : by rw [h a hnpa]
        ... = accum f (a :: as) : rfl
    )

lemma accum_perm {l₁ l₂ : list α} (hperm : list.perm l₁ l₂) : accum f l₁ = accum f l₂ :=
  list.perm.rec_on hperm
    /- perm.nil -/ rfl
    /- perm.cons -/ (
      λ a l₁ l₂ hperm h_ind,
        by dsimp [accum,list.foldr] at *; rw [h_ind]
    )
    /- perm.head -/ (
      λ a b l,
        by dsimp [accum,list.foldr];
           rw [←add_assoc];
           rw [add_comm (f a) (f b)];
           rw [add_assoc]
    )
    /- perm.trans -/ (λ _ _ _ _ _, flip eq.trans)

lemma accum_partition (p : α → Prop) [decidable_pred p] : ∀ (l : list α), accum f l = accum f (l.filter p) + accum f (l.filter (not∘ p)) :=
  begin
    intros l,
    let hperm := list.perm.append_partition p l,
    rw [list.partition_eq_filter_filter_safe] at hperm,
    dsimp [function.uncurry] at hperm,
    rw [←accum_perm hperm, ←accum_append],
    refl
  end

end
