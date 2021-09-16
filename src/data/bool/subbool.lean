import logic.funrel

/-!
 * bool supported on a truth value.
--/

@[reducible]
definition subbool (p : Prop) : Type := {b // p ∨ b=ff}

instance (p : Prop) : inhabited (subbool p) := inhabited.mk ⟨ff,or.inr rfl⟩
instance (p : Prop) : has_zero (subbool p) := has_zero.mk ⟨ff,or.inr rfl⟩
instance (p : Prop) : decidable_eq (subbool p) :=
  λ a b, @decidable.cases_on (a.val=b.val) (λ_, decidable (a=b)) (bool.decidable_eq a.val b.val) (λ hn, is_false (λ (h : a=b), hn (congr (@rfl _ subtype.val) h))) (λ h, is_true (subtype.eq h))

instance : subsingleton (subbool false) :=
  begin
    constructor,
    intros a b,
    apply subtype.eq,
    apply a.property.elim; try { exact false.elim },
    apply b.property.elim; try { exact false.elim },
    intros hb ha,
    rw [hb, ha]
  end

namespace subbool

@[reducible,inline]
protected
definition ff (p : Prop) : subbool p := ⟨ff,or.inr rfl⟩

@[reducible,inline]
protected
definition tt {p : Prop} : p → subbool p := λ h, ⟨tt,or.inl h⟩

@[reducible]
protected
definition and {p : Prop} : subbool p → subbool p → subbool p
| ⟨tt,hl⟩ ⟨tt,_⟩ := ⟨tt,or.elim hl or.inl (λ tf, bool.no_confusion tf)⟩
| _ _ := ⟨ff,or.inr rfl⟩

@[reducible]
protected
definition or {p : Prop} : subbool p → subbool p → subbool p
| ⟨ff,_⟩ ⟨ff,_⟩ := ⟨ff, by right; refl⟩
| ⟨ff,_⟩ ⟨tt,qt⟩ := ⟨tt, qt.elim _root_.or.inl (λ tf, bool.no_confusion tf)⟩
| ⟨tt,qt⟩ ⟨ff,_⟩ := ⟨tt, qt.elim _root_.or.inl (λ tf, bool.no_confusion tf)⟩
| ⟨tt,qt⟩ ⟨tt,_⟩ := ⟨tt, qt.elim _root_.or.inl (λ tf, bool.no_confusion tf)⟩

@[reducible]
definition xor {p : Prop} : subbool p → subbool p → subbool p
| ⟨ff,_⟩ ⟨ff,_⟩ := ⟨ff, or.inr rfl⟩
| ⟨ff,_⟩ ⟨tt,qt⟩ := ⟨tt, or.elim qt or.inl (λ tf, bool.no_confusion tf)⟩
| ⟨tt,qt⟩ ⟨ff,_⟩ := ⟨tt, or.elim qt or.inl (λ tf, bool.no_confusion tf)⟩
| ⟨tt,_⟩ ⟨tt,_⟩ := ⟨ff, or.inr rfl⟩

@[simp]
protected
lemma xor_ff {p : Prop} (a : subbool p) : xor a ⟨ff,or.inr rfl⟩ = a :=
  by cases a; cases a_val; unfold xor

@[simp]
protected
lemma ff_xor {p : Prop} (a : subbool p) : xor ⟨ff,or.inr rfl⟩ a = a :=
  by cases a; cases a_val; unfold xor

@[simp]
protected
lemma xor_self {p : Prop} (a : subbool p) : xor a a = ⟨ff,or.inr rfl⟩ :=
  by cases a; cases a_val; unfold xor

protected
lemma xor_comm {p : Prop} (a b : subbool p) : xor a b = xor b a :=
  by cases a; cases a_val; cases b; cases b_val; unfold xor

protected
lemma xor_assoc {p : Prop} (a b c : subbool p) : xor (xor a b) c = xor a (xor b c) :=
  by cases a; cases a_val; cases b; cases b_val; cases c; cases c_val; unfold xor

--- Relax the restriction on the support.
@[reducible]
definition relax {p q : Prop} (hpq : p → q) : subbool p → subbool q
| ⟨a,ha⟩ := ⟨a, ha.elim (or.inl ∘ hpq) or.inr⟩

@[reducible,inline]
definition to_bool {p : Prop} : subbool p → bool := subtype.val

@[reducible]
definition from_bool (p : Prop) : bool → subbool true := λ x, ⟨x,or.inl true.intro⟩

end subbool
