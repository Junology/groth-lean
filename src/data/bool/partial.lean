
@[reducible]
definition bool_p (p : Prop) : Type := {b // p ∨ b=ff}

@[reducible]
definition bxor_p {p : Prop} : bool_p p → bool_p p → bool_p p
| ⟨ff,_⟩ ⟨ff,_⟩ := ⟨ff, or.inr rfl⟩
| ⟨ff,qf⟩ ⟨tt,qt⟩ := ⟨tt, or.elim qt (or.inl) (λ tf, bool.no_confusion tf)⟩
| ⟨tt,qt⟩ ⟨ff,qf⟩ := ⟨tt, or.elim qt (or.inl) (λ tf, bool.no_confusion tf)⟩
| ⟨tt,_⟩ ⟨tt,_⟩ := ⟨ff, or.inr rfl⟩

@[reducible]
definition ff_p (p : Prop) : bool_p p := ⟨ff,or.inr rfl⟩

@[reducible]
definition tt_p {p : Prop} : p → bool_p p := λ h, ⟨tt,or.inl h⟩

@[simp]
lemma bxor_p_ff {p : Prop} (a : bool_p p) : bxor_p a ⟨ff,or.inr rfl⟩ = a :=
  by cases a; cases a_val; unfold bxor_p

@[simp]
lemma ff_bxor_p {p : Prop} (a : bool_p p) : bxor_p ⟨ff,or.inr rfl⟩ a = a :=
  by cases a; cases a_val; unfold bxor_p

@[simp]
lemma bxor_p_self {p : Prop} (a : bool_p p) : bxor_p a a = ⟨ff,or.inr rfl⟩ :=
  by cases a; cases a_val; unfold bxor_p

@[simp]
lemma bxor_p_comm {p : Prop} (a b : bool_p p) : bxor_p a b = bxor_p b a :=
  by cases a; cases a_val; cases b; cases b_val; unfold bxor_p

@[simp]
lemma bxor_p_assoc {p : Prop} (a b c : bool_p p) : bxor_p (bxor_p a b) c = bxor_p a (bxor_p b c) :=
  by cases a; cases a_val; cases b; cases b_val; cases c; cases c_val; unfold bxor_p
#print axioms bxor_p_ff
#print axioms ff_bxor_p
#print axioms bxor_p_self
#print axioms bxor_p_comm
#print axioms bxor_p_assoc
