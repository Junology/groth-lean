
lemma bool.eq_iff : ∀ (x y : bool), x = y ↔ (x = tt ∧ y = tt) ∨ (x = ff ∧ y = ff)
| ff ff := ⟨(λ _, or.inr ⟨rfl,rfl⟩),(λ _, rfl)⟩
| ff tt :=
  {
    mp := λ h, bool.no_confusion h,
    mpr := λ h, or.elim h (λ k, k.left) (λ k, k.right.symm)
  }
| tt ff :=
  {
    mp := λ h, bool.no_confusion h,
    mpr := λ h, or.elim h (λ k, k.right.symm) (λ k, k.left)
  }
| tt tt := ⟨(λ _, or.inl ⟨rfl,rfl⟩),(λ _, rfl)⟩

lemma bool.neq_iff : ∀ (x y : bool), x ≠ y ↔ (x = tt ∧ y = ff) ∨ (x = ff ∧ y = tt)
| ff ff :=
  {
    mp := λ h, false.elim (h rfl),
    mpr := λ h, or.elim h
             (λ k, bool.no_confusion k.left)
             (λ k, bool.no_confusion k.right)
  }
| ff tt := ⟨(λ _, or.inr ⟨rfl,rfl⟩),(λ _ h, bool.no_confusion h)⟩
| tt ff := ⟨(λ _, or.inl ⟨rfl,rfl⟩),(λ _ h, bool.no_confusion h)⟩
| tt tt :=
  {
    mp := λ h, false.elim (h rfl),
    mpr := λ h, or.elim h
             (λ k, bool.no_confusion k.right)
             (λ k, bool.no_confusion k.left)
  }

lemma eq_tt_of_not_eq_ff_safe : ∀ (x : bool), x ≠ ff → x = tt
| ff h := false.elim $ h rfl
| tt h := rfl

lemma eq_ff_of_not_eq_tt_safe : ∀ (x : bool), x ≠ tt → x = ff
| ff h := rfl
| tt h := false.elim $ h rfl

lemma neq_tt_iff : ∀ (x : bool), x ≠ tt ↔ x = ff
| ff := ⟨(λ _, rfl),(λ _ h, bool.no_confusion h)⟩
| tt := ⟨(λ h, false.elim (h rfl)),(λ h, bool.no_confusion h)⟩

lemma neq_ff_iff : ∀ (x : bool), x ≠ ff ↔ x = tt
| ff := ⟨(λ h, false.elim (h rfl)),(λ h, bool.no_confusion h)⟩
| tt := ⟨(λ _, rfl),(λ _ h, bool.no_confusion h)⟩

/- Lemmas on `bnot` -/
lemma eq_tt_of_bnot_eq_ff_safe : ∀ (x : bool), bnot x = ff → x = tt
| tt h := rfl
| ff h := bool.no_confusion h

lemma eq_ff_of_bnot_eq_tt_safe : ∀ (x : bool), bnot x = tt → x = ff
| tt h := bool.no_confusion h
| ff h := rfl

lemma bnot_eq_tt_iff : ∀ (x : bool), bnot x = tt ↔ x = ff
| tt := ⟨λ h, bool.no_confusion h, λ h, bool.no_confusion h⟩
| ff := ⟨λ _, rfl, λ _, rfl⟩

lemma bnot_eq_ff_iff : ∀ (x : bool), bnot x = ff ↔ x = tt
| tt := ⟨λ _, rfl, λ _, rfl⟩
| ff := ⟨λ h, bool.no_confusion h, λ h, bool.no_confusion h⟩

/- Lemmas on `bxor` -/
@[simp]
 lemma ff_bxor_safe : ∀ (a : bool), bxor ff a = a
| ff := rfl
| tt := rfl

@[simp]
lemma bxor_ff_safe : ∀ (a : bool), bxor a ff = a
| ff := rfl
| tt := rfl

@[simp]
lemma tt_bxor_safe : ∀ (a : bool), bxor tt a = bnot a
| tt := rfl
| ff := rfl

@[simp]
lemma bxor_tt_safe : ∀ (a : bool), bxor a tt = bnot a
| tt := rfl
| ff := rfl

@[simp]
lemma bxor_self_safe : ∀ (a : bool), bxor a a = ff
| ff := rfl
| tt := rfl

@[simp] lemma bxor_comm : ∀ a b, bxor a b = bxor b a :=
  by intros; cases b; cases a; refl

@[simp] lemma bxor_assoc : ∀ a b c, bxor (bxor a b) c = bxor a (bxor b c) :=
  by intros; cases c; cases b; cases a; refl

lemma bxor_eq_tt_iff : ∀ a b, bxor a b = tt ↔ a ≠ b
| ff ff := ⟨(λ h, bool.no_confusion h), (λ h, false.elim (h rfl))⟩
| ff tt := ⟨(λ _ h, bool.no_confusion h), (λ _, rfl)⟩
| tt ff := ⟨(λ _ h, bool.no_confusion h), (λ _, rfl)⟩
| tt tt := ⟨(λ h, bool.no_confusion h), (λ h, false.elim (h rfl))⟩

lemma bxor_eq_ff_iff : ∀ a b, bxor a b = ff ↔ a = b
| ff ff := ⟨(λ _, rfl), (λ _, rfl)⟩
| ff tt := ⟨(λ h, bool.no_confusion h), (λ h, bool.no_confusion h)⟩
| tt ff := ⟨(λ h, bool.no_confusion h), (λ h, bool.no_confusion h)⟩
| tt tt := ⟨(λ _, rfl), (λ _, rfl)⟩
