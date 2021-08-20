-- linear orders in the sense of nLab:
-- https://ncatlab.org/nlab/show/linear+order

import logic.definite_description

/-
 ******************
 ** Main classes **
 ******************
-/

@[reducible]
def idecidable_rel {α : Sort _} (r : α → α → Prop) :=
  ∀ a b, idecidable (r a b)

--- `is_linear_comparable X r` means the binary relation `r` on `X` satisfies the comparison axiom, which is involved with a kind of totality.
class is_linear_comparable (α : Type*) (r : α → α → Prop) : Prop :=
  (linear_comparable : ∀ a b c, r a b → r c b ∨ r a c)

--- `is_connected X r` means the binary relation `r` on `X` is connected; that is, the comparability under `r` is a tight apartness relation on `X`.
class is_connected (α : Type*) (r : α → α → Prop) : Prop :=
  (connected : ∀ a b, ¬ r a b → ¬ r b a → a = b)

--- `is_strict_linear_order X r` means the binary relation `r` on `X` is a linear order in the sense of nLab (see https://ncatlab.org/nlab/show/linear+order).
class is_strict_linear_order (α : Type*) (r : α → α → Prop) extends is_strict_order α r, is_asymm α r, is_linear_comparable α r, is_connected α r : Prop


/-
 ************
 ** Lemmas **
 ************
-/

-- trichotomous axiom and transitivity implies linearly comparability.
lemma is_linear_comparable_of_is_trichotomous_of_is_trans {α : Type*} (r : α → α → Prop) [is_trichotomous α r] [is_trans α r] : is_linear_comparable α r :=
  begin
    constructor,
    intros a b c hab,
    cases @trichotomous _ r _ a c with hac h,
    case or.inl {
      right; assumption
    },
    case or.inr {
      cases h with heq hca,
      case or.inl {
        rw heq at hab,
        left; assumption
      },
      case or.inr {
        have : r c b := trans hca hab,
        left; exact this
      }
    }
  end

-- Every trichotomous relation is connected
lemma is_connected_of_is_trichotomous {α : Type*} (r : α → α → Prop) [is_trichotomous α r] : is_connected α r :=
  begin
    constructor,
    intros a b hnab hnba,
    apply @eq_of_incomp α r _ a b,
    exact and.intro hnab hnba
  end

lemma is_incomp_trans_of_is_connected {α : Type*} (r : α → α → Prop) [hc : is_connected α r] : is_incomp_trans α r :=
  begin
    constructor,
    intros a b c hab hbc,
    have : a=b := @is_connected.connected _ _ hc _ _ hab.left hab.right,
    rw [this],
    assumption
  end

instance idecidable_of_is_trichotomous_of_is_asymm {α : Type*} (r : α → α → Prop) [is_trichotomous α r] [is_asymm α r] : idecidable_rel r :=
  begin
    intros a b,
    cases @trichotomous α r _ a b,
    case or.inl { constructor; left; assumption },
    case or.inr {
      constructor; right,
      cases h,
      case or.inl {
        cases h,
        intros h,
        exact absurd h (asymm h),
      },
      case or.inr { exact asymm h }
    }
  end

lemma is_trichotomous_of_is_connected {α : Type*} (r : α → α → Prop) [decr : idecidable_rel r] [is_connected α r] : is_trichotomous α r :=
  begin
    constructor,
    intros a b,
    cases (decr a b).is_either with _ hnab,
    case or.inl { left; assumption },
    case or.inr {
      cases (decr b a).is_either with _ hnba,
      case or.inl { right; right; assumption },
      case or.inr {
        right; left,
        exact is_connected.connected a b hnab hnba
      }
    }
  end

/-
 *******************
 ** Main theorems **
 *******************
-/

instance is_strict_linear_order_of_is_strict_total_order {α : Type*} (r : α → α → Prop) [hsto : is_strict_total_order α r] : is_strict_linear_order α r :=
  {
    to_is_strict_order := hsto.to_is_strict_order,
    to_is_asymm := is_asymm_of_is_trans_of_is_irrefl,
    to_is_linear_comparable :=
      is_linear_comparable_of_is_trichotomous_of_is_trans r,
    to_is_connected :=
      is_connected_of_is_trichotomous r
  }

instance is_strict_total_order_of_is_strict_linear_order {α : Type*} (r : α → α → Prop) [idecidable_rel r] [hslo : is_strict_linear_order α r] : is_strict_total_order α r :=
  {
    to_is_strict_weak_order :=
      {
        to_is_strict_order := hslo.to_is_strict_order,
        to_is_incomp_trans := is_incomp_trans_of_is_connected r,
      },
    to_is_trichotomous := is_trichotomous_of_is_connected r
  }
