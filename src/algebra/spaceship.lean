--================================================--
-- Spaceship operator (aka. three-way comparison) --
--================================================--

import algebra.linear_order
import logic.misc
import tactic.csimp

--- Spaceship operator (aka. three-way comparison).
class has_spaceship (α : Type*) :=
  (spaceship : α → α → ordering)

--- The spaceship operator has the same priority as ` < `
infix ` <=> `:50 := has_spaceship.spaceship

--- spaceship operator gives rise to strict ordering.
instance lt_of_spaceship (α : Type*) [has_spaceship α] : has_lt α :=
  { lt := λ x y, (x <=> y) = ordering.lt }

--- spaceship operator gives rise to ordering.
instance le_of_spaceship (α : Type*) [has_spaceship α] : has_le α :=
  { le := λ x y, (x <=> y) = ordering.lt ∨ (x <=> y) = ordering.eq }


/-
 - Properties of spaceship operators
 -/
namespace spaceship

protected
class is_trans (α : Type*) (ss : α → α → ordering) : Prop :=
  (htrans : ∀ o a b c, ss a b = o → ss b c = o → ss a c = o)

protected
class is_refl (α : Type*) (ss : α → α → ordering) : Prop :=
  (hrefl : ∀ a, ss a a = ordering.eq)

protected
class is_antisymm (α : Type*) (ss : α → α → ordering) : Prop :=
  (hantisymm : ∀ a b, ss a b = ordering.eq → a=b)

protected
class is_asymm (α : Type*) (ss : α → α → ordering) : Prop :=
  (hasymm : ∀ a b, ss a b = (ss b a).swap)

protected
class is_linear (α : Type*) (ss : α → α → ordering) extends is_trans α ss, is_refl α ss, is_antisymm α ss : Prop

protected
definition trans {α : Type*} (ss : α → α → ordering) [is_trans α ss] : ∀ {o a b c}, ss a b = o → ss b c = o → ss a c = o :=
  is_trans.htrans

protected
definition refl {α : Type*} (ss : α → α → ordering) [is_refl α ss] : ∀ {a}, ss a a = ordering.eq
  := @is_refl.hrefl α ss _

protected
definition antisymm {α : Type*} (ss : α → α → ordering) [is_antisymm α ss] : ∀ {a b}, ss a b = ordering.eq → a=b :=
  is_antisymm.hantisymm

protected
definition asymm {α : Type*} (ss : α → α → ordering) [is_asymm α ss] : ∀ {a b}, ss a b = (ss b a).swap :=
  is_asymm.hasymm

instance is_asymm_of_is_linear {α : Type*} (ss : α → α → ordering) [is_linear α ss] : is_asymm α ss :=
  begin
    constructor,
    intros a b,
    cases hab: ss a b,
    case ordering.lt {
      cases hba: ss b a,
      case ordering.lt {
        have : ss a a = ordering.lt,
          from spaceship.trans ss hab hba,
        rw [spaceship.refl ss] at this,
        injection this
      },
      case ordering.eq {
        have : b=a, from spaceship.antisymm ss hba,
        rw [this, spaceship.refl ss] at hab,
        injection hab
      },
      case ordering.gt { refl }
    },
    case ordering.eq {
      cases hba: ss b a,
      case ordering.lt {
        rw [spaceship.antisymm ss hab, spaceship.refl ss] at hba,
        injection hba
      },
      case ordering.eq { refl },
      case ordering.gt {
        rw [spaceship.antisymm ss hab, spaceship.refl ss] at hba,
        injection hba
      }
    },
    case ordering.gt {
      cases hba: ss b a,
      case ordering.lt { refl },
      case ordering.eq {
        rw [spaceship.antisymm ss hba, spaceship.refl ss] at hab,
        injection hab
      },
      case ordering.gt {
        have : ss a a = ordering.gt,
          from spaceship.trans ss hab hba,
        rw [spaceship.refl ss] at this,
        injection this
      }
    }
  end

end spaceship


instance is_antisymm_of_is_trichotomous {α : Type*} (r : α → α → Prop) [htric : is_trichotomous α r] [decidable_rel r] : spaceship.is_antisymm α (cmp_using r) :=
  begin
    constructor,
    intros a b,
    cases h: cmp_using r a b,
    case ordering.lt { intros ho; injection ho },
    case ordering.gt { intros ho; injection ho },
    case ordering.eq {
      intros,
      delta cmp_using at h,
      by_cases hrab: r a b; by_cases hrba: r b a;
        try {rw [ite_eval_true hrab] at h};
        try {rw [ite_eval_false hrab] at h};
        try {rw [ite_eval_true hrba] at h};
        try {rw [ite_eval_false hrba] at h};
        try {injection h},
      apply or.elim (@trichotomous _ r _ a b); try {intro h; apply or.elim h},
      all_goals { intro; try {contradiction}; try {assumption}}
    }
  end

instance is_refl_of_is_irrefl {α : Type*} (r : α → α → Prop) [is_irrefl α r] [decidable_rel r] : spaceship.is_refl α (cmp_using r) :=
  begin
    constructor,
    intros a,
    delta cmp_using,
    have hnraa : ¬ r a a := irrefl a,
    rw [ite_eval_false hnraa, ite_eval_false hnraa],
  end

instance is_trans_of_is_trans {α : Type*} (r : α → α → Prop) [is_trans α r] [is_incomp_trans α r] [decidable_rel r] : spaceship.is_trans α (cmp_using r) :=
  begin
    constructor,
    intros o a b c hab hbc,
    unfold cmp_using at *,
    cases o,
    case ordering.lt {
      by_cases hrab: r a b; by_cases hrba: r b a;
        by_cases hrbc: r b c; by_cases hrcb: r c b,
      all_goals {
        try {rw [ite_eval_true hrab] at hab},
        try {rw [ite_eval_false hrab] at hab},
        try {rw [ite_eval_true hrba] at hab},
        try {rw [ite_eval_false hrba] at hab},
        try {rw [ite_eval_true hrbc] at hbc},
        try {rw [ite_eval_false hrbc] at hbc},
        try {rw [ite_eval_true hrcb] at hbc},
        try {rw [ite_eval_false hrcb] at hbc},
        try {contradiction}
      },
      all_goals {
        have : r a c,
          from trans hrab hrbc,
        rw [ite_eval_true this]
      },
    },
    case ordering.eq {
      by_cases hrab: r a b; by_cases hrba: r b a;
        by_cases hrbc: r b c; by_cases hrcb: r c b,
      all_goals {
        try {rw [ite_eval_true hrab] at hab},
        try {rw [ite_eval_false hrab] at hab},
        try {rw [ite_eval_true hrba] at hab},
        try {rw [ite_eval_false hrba] at hab},
        try {rw [ite_eval_true hrbc] at hbc},
        try {rw [ite_eval_false hrbc] at hbc},
        try {rw [ite_eval_true hrcb] at hbc},
        try {rw [ite_eval_false hrcb] at hbc},
        try {contradiction}
      },
      have hac : ¬r a c ∧ ¬r c a,
        from incomp_trans (and.intro hrab hrba) (and.intro hrbc hrcb),
      rw [ite_eval_false hac.left, ite_eval_false hac.right],
    },
    case ordering.gt {
      by_cases hrab: r a b; by_cases hrba: r b a;
        by_cases hrbc: r b c; by_cases hrcb: r c b,
      all_goals {
        try {rw [ite_eval_true hrab] at hab},
        try {rw [ite_eval_false hrab] at hab},
        try {rw [ite_eval_true hrba] at hab},
        try {rw [ite_eval_false hrba] at hab},
        try {rw [ite_eval_true hrbc] at hbc},
        try {rw [ite_eval_false hrbc] at hbc},
        try {rw [ite_eval_true hrcb] at hbc},
        try {rw [ite_eval_false hrcb] at hbc},
        try {contradiction}
      },
      have hrca : r c a,
        from trans hrcb hrba,
      have : ¬r a c, {
        intros hrac,
        have : r a b,
          from trans hrac hrcb,
        contradiction
      },
      rw [ite_eval_false this, ite_eval_true hrca]
    }
  --/
  end

namespace unsafe

instance is_linear_of_is_strict_total_order {α : Type*} (r : α → α → Prop) [is_strict_total_order α r] : spaceship.is_linear α (cmp_using r) :=
  { /- auto generated -/ }

end unsafe

#print axioms is_antisymm_of_is_trichotomous
#print axioms is_refl_of_is_irrefl
#print axioms is_trans_of_is_trans
#print axioms unsafe.is_linear_of_is_strict_total_order


