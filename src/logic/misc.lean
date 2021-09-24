
--- All equality are heterogeneously equal to `rfl`.
lemma eq_irrel {α : Sort _} : ∀ {x y : α} (hxy : x = y), hxy == @rfl α x
| _ _ rfl := heq.rfl

--- Eliminator of `ite` of predicators.
lemma ite_pred_iff {α : Sort _} {p : Prop} [decidable p] {P : α → Prop} : ∀ {x y}, (p → P x) ∧ (¬p → P y) ↔ P (ite p x y) :=
  begin
    intros x y,
    split,
    show _ → P (ite p x y), {
      intros hxy,
      by_cases p,
      rw [if_pos h]; exact hxy.left h,
      rw [if_neg h]; exact hxy.right h
    },
    show P (ite p x y) → _, {
      intros hP,
      by_cases p,
      rw [if_pos h] at hP; exact ⟨(λ _,hP),λ hn, false.elim (hn h)⟩,
      rw [if_neg h] at hP; exact ⟨false.elim ∘ h, (λ_,hP)⟩
    }
  end

lemma whether_of_ite {α : Sort _} {p : Prop} [decidable p] {P : α → Prop} : ∀ {x y}, P (ite p x y) → P x ∨ P y :=
  begin
    intros x y hP,
    by_cases p,
    rw [if_pos h] at hP; exact or.inl hP,
    rw [if_neg h] at hP; exact or.inr hP
  end

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

definition xor_self (p : Prop) : xor p p ↔ false :=
  begin
    split; intros h; try { contradiction },
    apply or.elim h; try { exact (and_not_self p).mp }
  end

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

lemma and_iff_left_of_imp {p q : Prop} : (p → q) → (p ∧ q ↔ p) :=
  λ hpq, iff.intro and.left (λ hp, ⟨hp,hpq hp⟩)

lemma and_iff_right_of_imp {p q : Prop} : (q → p) → (p ∧ q ↔ q) :=
  λ hqp, iff.intro and.right (λ hq, ⟨hqp hq, hq⟩)

lemma or_disproof_left {p q : Prop} (hnp : ¬p) : (p ∨ q) ↔ q :=
  iff.intro (or.rec (by intro; contradiction) id) or.inr

lemma or_disproof_right {p q : Prop} (hnp : ¬p) : (q∨ p) ↔ q :=
  iff.intro (or.rec id (by intro; contradiction)) or.inl

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

--- The equality on Σ-type from equality and heterogeneous equality.
lemma sigma_eq_heq {α : Sort _} {β : α → Sort _} : ∀ {x y : sigma β}, x.fst = y.fst → x.snd == y.snd → x = y
| ⟨x,hx⟩ ⟨y,hy⟩ rfl heq.rfl := rfl

--- Variant of `funext` with heterogeneous dependent domain.
lemma funext_hdom {α : Sort _} {β : α → Sort _} {γ : Sort _} : ∀ {a₁ a₂ : α} {f : β a₁ → γ} {g : β a₂ → γ}, a₁ = a₂ → (∀ (x : β a₁) (y : β a₂), x == y → f x = g y) → f == g
| _ _ f g rfl hfg := heq_of_eq $ funext (λ x, hfg x x heq.rfl)
