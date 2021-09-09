
import logic.idecidable

class is_subfinite (α : Sort _) : Prop :=
  (natemb : ∃ (n : ℕ) (f : α → ℕ), ∀ a, (f a < n) ∧ (∀ b, f a = f b → a = b))

lemma natemb (α : Sort _) [is_subfinite α] : ∃ (n : ℕ) (f : α → ℕ), ∀ a, (f a < n) ∧ (∀ b, f a = f b → a = b) := is_subfinite.natemb

--- Every subsingleton type is subfinite
instance subsingleton_is_subfinite (α : Sort _) [subsingleton α] : is_subfinite α :=
  begin
    constructor,
    existsi 1,
    existsi (λ_, 0),
    intros a,
    dsimp *,
    split; try { exact nat.zero_lt_one },
    intros b _,
    exact subsingleton.elim a b
  end

--- Every subtype of a subfinite type is again subfinite
instance subfinite_sub (α : Sort _) [is_subfinite α] (p : α → Prop) : is_subfinite {a // p a} :=
  begin
    cases natemb α with n hn; cases hn with f hf,
    constructor,
    existsi n; existsi (f∘subtype.val),
    intros a,
    dunfold function.comp,
    split; try { exact (hf a.val).left },
    intros b hfab,
    apply subtype.eq,
    exact (hf a.val).right b.val hfab,
  end

--- Every subfinite type has internally decidable equality.
theorem subfinite_idecidable_eq (α : Sort _) [is_subfinite α] : idecidable_eq α :=
  begin
    cases natemb α with n hn; cases hn with f hf,
    intros a b,
    constructor,
    by_cases (f a = f b),
    focus /- `f a = f b` -/ {
      exact or.inl ((hf a).right b h)
    },
    focus /- `f a ≠ f b` -/ {
      apply or.inr,
      intros hab,
      have : f a = f b := congr rfl hab,
      contradiction
    }
  end

#print axioms subfinite_idecidable_eq
