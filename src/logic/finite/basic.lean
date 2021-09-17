import function.misc
import function.bijection
import data.list.misc
import data.list.map_partial
import data.finite.finord

--- Exhaustive list of elements of given type; i.e. a list that contains all the terms of given type with no duplicate entries.
@[reducible,inline]
definition exhaustive_list (α : Type _) := {l : list α // l.nodup ∧ ∀ x, x ∈ l}

--- The standard exhaustive list of elements of type `finord n`.
protected
definition finord.exhaustive_list (n : ℕ) : exhaustive_list (finord n) :=
  nat.rec_on n
    /- n=0 -/ ⟨[],⟨list.nodup.nil, λ x, by cases x⟩⟩
    /- n=k+1 -/ (
      λ k l_ind, subtype.mk (finord.fz :: l_ind.val.map finord.fs) $
        begin
          split,
          show list.nodup _, {
            refine list.nodup.cons _ _,
            exact list.not_mem_map_of_offimage finord.fz (@finord.fz_not_fs k),
            exact list.nodup_map_of_nodup finord.fs_inj l_ind.property.left
          },
          show ∀ x, x ∈ _, {
            intros x; cases x with _ _ j,
            exact or.inl rfl,
            exact or.inr (list.mem_map_of_mem j _ (l_ind.property.right j))
          }
        end
    )

namespace exhaustive_list

protected
lemma nodup {α : Type _} (l : exhaustive_list α) : l.val.nodup := l.property.left

protected
lemma exhaustive {α : Type _} (l : exhaustive_list α) : ∀ x, x ∈ l.val := l.property.right

--- `exhaustive_list α` is, if any, unique up to permutations.
protected
lemma perm {α : Type _} (l l': exhaustive_list α) : l.val.perm l'.val :=
  list.nodup_perm_of_mem l.nodup l'.nodup $
    λ x, calc
      x ∈ l.val ↔ true : iff_true_intro (l.exhaustive x)
      ...       ↔ x ∈ l'.val : (iff_true_intro (l'.exhaustive x)).symm

--- Translate `exhaustive_list` along bijections.
protected
definition translate {α β : Type _} {f : α → β} : function.bijective f → exhaustive_list α → exhaustive_list β :=
  λ hbij l, subtype.mk (l.val.map f) $
    begin
      split,
      show list.nodup _, {
        exact list.nodup_map_of_nodup hbij.left l.property.left
      },
      show ∀ x, x ∈ _, {
        intros x,
        cases hbij.right x with y hy; rw [←hy],
        apply list.mem_map_of_mem _ _ (l.property.right y),
      }
    end

--- If `α` has an `exhaustive_list`, then each decidable subtype of `α` does.
protected
definition subtype {α : Type _} (l : exhaustive_list α) (p : α → Prop) [decidable_pred p] : exhaustive_list (subtype p) :=
  subtype.mk (l.val.filter_to_subtype p) $
    begin
      split,
      exact list.nodup_map_partial_of_nodup (function.partial.coinj_inj) l.property.left,
      intros x,
      have hx : (function.partial.coinj p).is_defined_at x.val,
        from (function.partial.coinj_domain x.val).mpr x.property,
      have : x = (function.partial.coinj p).to_fun ⟨x.val,hx⟩, {
        symmetry,
        suffices : function.partial.coinj p x.val = some x,
          from (function.partial.coinj p).to_fun_value_of_eq this,
        cases hinjx : function.partial.coinj p x.val with y,
        exfalso; exact hx hinjx,
        dunfold function.partial.coinj at hinjx,
        rw [dif_pos x.property] at hinjx,
        apply congr_arg some; apply subtype.eq,
        let hyxval := congr_arg subtype.val (option.some.inj hinjx.symm),
        exact hyxval,
      },
      rw [this],
      refine list.mem_map_partial_of_mem _ _ _,
      exact l.property.right _
    end

end exhaustive_list


--- Class for types that are isomorphic to `finord n` for some `n`.
class is_finite (α : Type _) : Prop :=
  (isom_to_finord : ∃ (n : ℕ), nonempty (bijection α (finord n)))

instance finord_is_finite {n : ℕ} : is_finite (finord n) :=
  is_finite.mk ⟨n, nonempty.intro bijection.id⟩

@[reducible,inline]
definition isom_to_finord (α : Type _) [is_finite α] : ∃ (n : ℕ), nonempty (bijection α (finord n)) :=
  is_finite.isom_to_finord

namespace is_finite

variables {α : Type _} [is_finite α]

lemma replace_finord {motive : ℕ → Prop} : (∀ n, finord n → motive n) → α → ∃ n, motive n :=
  begin
    intros h a,
    cases _root_.isom_to_finord α with n e_f,
    cases e_f with f,
    exact ⟨n, h n (f.to_fun a)⟩
  end

--- Every finite type admits a complete list of elements.
lemma has_exhaustive_list : nonempty (exhaustive_list α) :=
  begin
    cases _root_.isom_to_finord α with n e_f,
    cases e_f with f,
    constructor,
    apply exhaustive_list.translate f.inv_is_bijective,
    exact finord.exhaustive_list n,
  end

end is_finite
