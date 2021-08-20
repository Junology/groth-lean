
--- Statement of definite description
axiom definite_description {α : Type*} {p : α → Prop} : (∃! (a : α), p a) → {a:α // p a}

--- An "internal" version of decidability.
class idecidable (p : Prop) : Prop :=
  (is_either : p ∨ ¬ p)

lemma whether (p : Prop) [idec : idecidable p] : p ∨ ¬ p :=
  idec.is_either

namespace unsafe

/-- Turn the "internal" decidablility into the "external" one. This uses `propext` as well as `definite_description`. -/
noncomputable instance decidable_of_idecidable (p : Prop) [idecidable p] : decidable p :=
  begin
    refine subtype.val (@definite_description (decidable p) (λ x, @ite _ p x true false ↔ p) _),
    cases whether p with hp hnp,
    case or.inl {
      existsi is_true hp,
      simp [ite],
      split; try { assumption },
      intros hdec hpiff,
      cases hdec,
      case is_true { refl },
      case is_false { contradiction }
    },
    case or.inr {
      existsi is_false hnp,
      simp [ite],
      split; try { assumption },
      intros hdec hpiff,
      cases hdec,
      case is_true { contradiction },
      case is_false { refl }
    }
  end

end unsafe
