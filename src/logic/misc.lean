
attribute [simp]
definition ite_eval_true {p : Prop} [pdec : decidable p] {α : Type*} : p → ∀ (a b : α), ite p a b = a :=
  begin
    intros hp a b,
    delta ite,
    cases hd: pdec with h hn,
    case is_false { contradiction },
    case is_true { dsimp [], refl }
  end

attribute [simp]
definition ite_eval_false {p : Prop} [pdec : decidable p] {α : Type*} : (¬p) → ∀ (a b: α), ite p a b = b :=
  begin
    intros hnp a b,
    delta ite,
    cases hd: pdec with hp1 hnp1,
    case is_false { dsimp [], refl },
    case is_true { contradiction }
  end

definition xor_congr {p q p' q' : Prop} : (p ↔ p') → (q ↔ q') → (xor p q ↔ xor p' q') :=
  begin
    intros hp hq,
    have hnp : ¬p ↔ ¬p', from not_congr hp,
    have hnq : ¬q ↔ ¬q', from not_congr hq,
    apply or_congr; apply and_congr; try { assumption },
  end

#print axioms xor_congr

definition xor_self (p : Prop) : xor p p ↔ false :=
  begin
    split; intros h; try { contradiction },
    apply or.elim h; try { exact (and_not_self p).mp }
  end

#print axioms xor_self

definition xor_comm (p q : Prop) : xor p q ↔ xor q p :=
  begin
    dunfold xor,
    exact or.comm,
  end

definition false_xor (p : Prop) : xor false p ↔ p :=
  begin
    split,
    show xor false p → p, {
      dunfold xor; intro h; apply or.elim h,
      exact (false.elim ∘ and.left),
      exact and.left
    },
    show p → xor false p, {
      dunfold xor; intro h,
      right,
      exact ⟨h, false.elim⟩
    }
  end

definition xor_false (p : Prop) : xor p false ↔ p :=
  by calc
    xor p false
        ↔ xor false p : xor_comm p false
    ... ↔ p : false_xor p

#print axioms false_xor
#print axioms xor_false

#check or_assoc

lemma not_or_distrib {p q : Prop} : ¬(p∨q) ↔ (¬p)∧(¬q) :=
  begin
    constructor,
    show ¬(p∨ q) → (¬p)∧(¬q), {
      intros hpq,
      split,
      show ¬p, { intros hp, have : p∨ q, by left; assumption, contradiction },
      show ¬q, { intros hq, have : p∨ q, by right; assumption, contradiction },
    },
    show (¬p)∧(¬q) → ¬(p∨ q), {
      intros hnpq hpq,
      exact or.elim hpq hnpq.left hnpq.right
    },
  end

#print axioms not_or_distrib

#check or_iff_left_of_imp

lemma and_iff_left_of_imp {p q : Prop} : (p → q) → (p ∧ q ↔ p) :=
  λ hpq, iff.intro and.left (λ hp, ⟨hp,hpq hp⟩)

lemma and_iff_right_of_imp {p q : Prop} : (q → p) → (p ∧ q ↔ q) :=
  λ hqp, iff.intro and.right (λ hq, ⟨hqp hq, hq⟩)

#print axioms and_iff_left_of_imp
#print axioms and_iff_right_of_imp

lemma or_disproof_left {p q : Prop} (hnp : ¬p) : (p ∨ q) ↔ q :=
  iff.intro (or.rec (by intro; contradiction) id) or.inr

lemma or_disproof_right {p q : Prop} (hnp : ¬p) : (q∨ p) ↔ q :=
  iff.intro (or.rec id (by intro; contradiction)) or.inl

#print axioms or_disproof_left

lemma or_and_distrib {p q r : Prop} : (p ∨ q) ∧ r ↔ (p ∧ r) ∨ (q ∧ r) :=
{
  mp :=
    λ hpqr,
      hpqr.left.elim
        (λ hp, or.inl ⟨hp,hpqr.right⟩)
        (λ hq, or.inr ⟨hq,hpqr.right⟩),
  mpr :=
    λ hprqr,
      hprqr.elim
        (λ hpr, ⟨or.inl hpr.left, hpr.right⟩)
        (λ hqr, ⟨or.inr hqr.left, hqr.right⟩)
}

#print axioms or_and_distrib
