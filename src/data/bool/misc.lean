
@[simp]
 lemma ff_bxor_safe : ∀ (a : bool), bxor ff a = a
| ff := rfl
| tt := rfl

@[simp]
lemma bxor_ff_safe : ∀ (a : bool), bxor a ff = a
| ff := rfl
| tt := rfl

@[simp]
lemma bxor_self_safe : ∀ (a : bool), bxor a a = ff
| ff := rfl
| tt := rfl

@[simp] lemma bxor_comm : ∀ a b, bxor a b = bxor b a :=
  by intros; cases b; cases a; refl

@[simp] lemma bxor_assoc : ∀ a b c, bxor (bxor a b) c = bxor a (bxor b c) :=
  by intros; cases c; cases b; cases a; refl
