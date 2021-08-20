
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

