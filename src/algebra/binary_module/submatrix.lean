import logic.funrel
import logic.finite
import logic.idecidable
import .basic .bool .decfree

namespace binary_module

local attribute [instance] binary_abelian

--- Type for matrices whose entries are indexed in subtypes of `finord`. This is defined so that `matrix p q` is isomorphic to the type of homomorphisms from the free `binary_module` generated by `subtype q` to that by `subtype p`.
definition submatrix {m n : ℕ} (p : finord m → Prop) (q : finord n → Prop) : Type _ :=
  {a : finord m → subtype q → bool // ∀ i y, a i y ≠ 0 → p i}


namespace submatrix

variables {m n : ℕ} {p : finord m → Prop} {q : finord n → Prop}

--- In each column, 'non-zero' is a decidable condition.
instance col_decidable_neq_zero (a : submatrix p q) (y : subtype q) : decidable_pred (λ i, p i ∧ a.val i y ≠ 0) :=
  begin
    intros i; dsimp *,
    cases bool.decidable_eq (a.val i y) 0 with haiy haiy,
    case is_false {
      exact is_true ⟨a.property _ _ haiy, haiy⟩,
    },
    case is_true {
      apply is_false,
      intros h,
      exact h.right haiy
    }
  end

--- The 'support' of each column; i.e. the `exhaustive_list` of non-zero entries.
definition col_support (a : submatrix p q) (y : subtype q) : exhaustive_list {x : subtype p // a.val x.val y ≠ 0} :=
  exhaustive_list.translate
    (@bijection.subtype_uncurry _ p (λ i, a.val i y ≠ 0)).inv_is_bijective
    ((finord.exhaustive_list m).restrict (λ i, p i ∧ a.val i y ≠ 0))

--- In each column of `submatrix`, only finitely many entries are non-zero.
lemma col_finite (a : submatrix p q) (y : subtype q) : is_finite {x : subtype p // a.val x.val y ≠ 0} :=
  is_finite.of_exhaustive_list (a.col_support y)

--- Realize matrices as maps into free modules generated by the row indices (aka. Kleisli arrows).
definition to_fun (a : submatrix p q) : subtype q → finsupp_bits (subtype p) :=
  λ y, subtype.mk (λ (x : subtype p), a.val x.val y) $ a.col_finite y

--- For every term `finsupp_bits (subtype p)`, its support is internally-decidable in the super type.
lemma support_idec {α : Type _} (f : α → finsupp_bits (subtype p)) (a : α): ∀ (i : finord m), idecidable (∃ (h : p i), (f a).val ⟨i,h⟩ ≠ 0) :=
  λ i, @is_finite.idec_in_super _ _ p (λ x, (f a).val x ≠ 0) (f a).property i

namespace unsafe

--- Representation matrix
noncomputable definition mk_mat (f : subtype q → finsupp_bits (subtype p)) : submatrix p q :=
{
  val := λ i y,
    decidable.cases_on
      (@unsafe.decidable_of_idecidable _ (support_idec f y i))
      (λ _, ff) (λ _, tt),
  property :=
    begin
      intros i y h,
      cases @whether _ (support_idec f y i) with hpi hnpi,
      case or.inl { cases hpi with hpi _, exact hpi },
      case or.inr {
        rw [@unsafe.dec_of_idec_neg _ (support_idec f y i) hnpi] at h,
        dsimp * at h,
        exfalso; exact h rfl
      }
    end
}

--- The representation matrix of a function defined from a matrix is exactly the original one.
lemma mat_of_to_fun (a : submatrix p q) : mk_mat a.to_fun = a :=
  begin
    apply subtype.eq,
    dsimp [mk_mat],
    funext,
    cases @whether _ (support_idec a.to_fun y i) with hpi hnpi,
    case or.inl {
      rw [@unsafe.dec_of_idec_pos _ (support_idec _ _ _) hpi],
      dsimp *,
      symmetry,
      cases hpi with hpi hai,
      dsimp [to_fun] at hai,
      exact (neq_ff_iff _).mp hai,
    },
    case or.inr {
      rw [@unsafe.dec_of_idec_neg _ (support_idec _ _ _) hnpi],
      dsimp *,
      symmetry,
      dsimp [to_fun] at hnpi,
      cases haiy: a.val i y,
      case ff { refl },
      case tt {
        exfalso; apply hnpi; clear hnpi,
        existsi a.property i y ((neq_ff_iff _).mpr haiy),
        rw [haiy],
        intro h; injection h,
      }
    }
  end

--- The function defined from a representation matrix is exactly the original one.
lemma to_fun_of_mat (f : subtype q → finsupp_bits (subtype p)) : (mk_mat f).to_fun = f :=
  begin
    funext y,
    apply subtype.eq,
    funext x,
    dsimp [mk_mat, to_fun],
    cases @whether _ (support_idec f y x.val) with hp hnp,
    case or.inl {
      rw [@unsafe.dec_of_idec_pos _ (support_idec _ _ _) hp],
      dsimp *,
      symmetry,
      cases hp with hpx hfy,
      rw [subtype.eta x hpx] at hfy,
      exact (neq_ff_iff _).mp hfy
    },
    case or.inr {
      rw [@unsafe.dec_of_idec_neg _ (support_idec _ _ _) hnp],
      dsimp *,
      symmetry,
      cases hfy: (f y).val x,
      case ff { refl },
      case tt {
        exfalso; apply hnp; clear hnp,
        existsi x.property,
        rw [subtype.eta x x.property],
        exact (neq_ff_iff _).mpr hfy,
      }
    }
  end

end unsafe

end submatrix

end binary_module
