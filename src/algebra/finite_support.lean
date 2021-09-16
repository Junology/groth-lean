import data.list.finord
import data.finite.finite

--- Structure to guarantee that a function is zero except on finitely many points.
structure finite_support {α β : Type _} [has_zero β] (f : α → β) :=
  (supp : list α)
  (nodup : supp.nodup)
  (complete : ∀ x, f x ≠ 0 ↔ x ∈ supp)

namespace finite_support

variables {α β : Type _} [has_zero β] {f : α → β}

--- A finite support of a function is, if any, unique up to `list.perm`.
protected
lemma unique_perm (fs₁ fs₂ : finite_support f) : list.perm fs₁.supp fs₂.supp :=
  list.nodup_perm_of_mem fs₁.nodup fs₂.nodup $ λ x,
    calc
      x ∈ fs₁.supp
          ↔ f x ≠ 0 : iff.symm (fs₁.complete x)
      ... ↔ x ∈ fs₂.supp : fs₂.complete x

--- Standard supports of functions out of `finord n`.
lemma of_finord_domain {n : ℕ} [decidable_eq β] (f : finord n → β) : finite_support f :=
{
  supp := (finord.elem_list n).filter (λ a, f a ≠ 0),
  nodup := list.nodup_filter (finord.elem_list_nodup n),
  complete :=
    begin
      intros x,
      symmetry,
      calc
        x ∈ list.filter (λ (a : finord n), f a ≠ 0) (finord.elem_list n)
            ↔ x ∈ finord.elem_list n ∧ f x ≠ 0 : list.mem_filter x
        ... ↔ true ∧ f x ≠ 0 : and_congr (iff_true_intro (finord.elem_list_complete _)) (iff.refl _)
        ... ↔ f x ≠ 0 : true_and _
    end
}

#print axioms of_finord_domain

end finite_support

--- Existence of finite support
@[reducible]
definition has_finite_support {α β : Type _} [has_zero β] (f : α → β) : Prop :=
  nonempty (finite_support f)

namespace has_finite_support

--- Every map out of a finite type admits a finite support.
lemma of_finite_domain {α β : Type _} [is_finite α] [has_zero β] [decidable_eq β] (f : α → β) : has_finite_support f :=
  begin
    cases @is_finite.has_element_list α _ with elem_list,
    constructor,
    refine finite_support.mk (elem_list.val.filter (λ x, f x ≠ 0)) _ _,
    show list.nodup _, {
      exact list.nodup_filter elem_list.property.left
    },
    show ∀ x, f x ≠ 0 ↔ _, {
      intros x,
      have hx : x ∈ elem_list.val := elem_list.property.right x,
      symmetry,
      calc
        x ∈ list.filter (λ (x : α), f x ≠ 0) elem_list.val
            ↔ x ∈ elem_list.val ∧ f x ≠ 0 : list.mem_filter x
        ... ↔ true ∧ f x ≠ 0 : and_congr (iff_true_intro hx) iff.rfl
        ... ↔ f x ≠ 0 : true_and _
    }
  end

#print axioms of_finite_domain

end has_finite_support
