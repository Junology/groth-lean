import logic.idecidable

--- Statement of definite description
axiom definite_description {α : Sort _} {p : α → Prop} : (∃! (a : α), p a) → {a:α // p a}

namespace unsafe

--- `definite_description` enables choice on subsingleton types.
noncomputable definition subsingleton_choice (α : Sort _) [subsingleton α] : nonempty α → α :=
  λ h, subtype.val ∘ @definite_description α (λ _, true) $
    by cases h with a; existsi a; split; try {trivial};
       dsimp *; intros y _; exact subsingleton.elim y a

--- Turn the "internal" decidablility into the "external" one.
noncomputable definition decidable_of_idecidable (p : Prop) [idecidable p] : decidable p :=
  subsingleton_choice (decidable p) $
    begin
      cases whether p with hp hnp,
      case or.inl {
        constructor,
        exact is_true hp,
      },
      case or.inr {
        constructor,
        exact is_false hnp,
      }
    end

lemma dec_of_idec_pos {p : Prop} [idecidable p] : Π (h : p), decidable_of_idecidable p = is_true h :=
  begin
    intros h,
    cases decidable_of_idecidable p with hnp hp,
    case is_false { exfalso; exact hnp h },
    case is_true { refl }
  end

lemma dec_of_idec_neg {p : Prop} [idecidable p] : Π (h : ¬p), decidable_of_idecidable p = is_false h :=
  begin
    intros h,
    cases decidable_of_idecidable p with hnp hp,
    case is_false { refl },
    case is_true { exfalso; exact h hp }
  end

end unsafe
