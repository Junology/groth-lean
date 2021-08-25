@[simp] lemma bxor_comm : ∀ a b, bxor a b = bxor b a :=
  by intros; cases b; cases a; refl

@[simp] lemma bxor_assoc : ∀ a b c, bxor (bxor a b) c = bxor a (bxor b c) :=
  by intros; cases c; cases b; cases a; refl
