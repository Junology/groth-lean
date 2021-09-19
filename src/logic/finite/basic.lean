import function.misc
import function.bijection
import data.list.misc
import data.list.map_partial
import data.list.index
import data.finord

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

--- Convert an `exhaustive_list` into a bijection out of a finite set.
protected
definition to_bijection {α : Type _} [decidable_eq α] (l : exhaustive_list α) : bijection (finord l.val.length) α :=
  (bijection.subtype_true α).comp $
    bijection.comp
      (@bijection.subtype_equiv _ (λ x, x ∈ l.val) (λ _, true) (λ x, iff_true_intro (l.property.right x)))
      (list.enum_bijection l.property.left)

end exhaustive_list


--- Class for types that are isomorphic to `finord n` for some `n`.
class is_finite (α : Type _) : Prop :=
  (enumerable : ∃ (n : ℕ) (f : finord n → α), function.bijective f)

instance finord_is_finite {n : ℕ} : is_finite (finord n) :=
  is_finite.mk ⟨n, id, bijection.id.is_bijective⟩

@[reducible,inline]
definition enumerable (α : Type _) [is_finite α] : ∃ (n : ℕ) (f : finord n → α), function.bijective f :=
  is_finite.enumerable

namespace is_finite

--- Every finite type must be internally decidable.
protected
lemma has_idecidable_eq {α : Type _} [is_finite α] : idecidable_eq α :=
  begin
    intros x y,
    constructor,
    cases _root_.enumerable α with n ef; cases ef with f hf,
    cases hf.right x with a ha,
    cases hf.right y with b hb,
    refine dite (a=b) _ _,
    show a = b → _, {
      intros hab,
      apply or.inl,
      calc
        x   = f a : ha.symm
        ... = f b : congr_arg f hab
        ... = y : hb
    },
    show a ≠ b → _, {
      intros hab,
      apply or.inr,
      intros hxy,
      refine hab (hf.left _),
      calc
        f a = x : ha
        ... = y : hxy
        ... = f b : hb.symm
    }
  end

--- Every finite type admits a complete list of elements.
lemma has_exhaustive_list (α : Type _) [is_finite α] : nonempty (exhaustive_list α) :=
  begin
    cases _root_.enumerable α with n ef; cases ef with f hf,
    constructor,
    apply exhaustive_list.translate hf,
    exact finord.exhaustive_list n,
  end

--- Given `exhausitve_list α`, one can conclude `α` is a finite type.
protected
theorem of_exhaustive_list {α : Type _} [decidable_eq α] (l : exhaustive_list α) : is_finite α :=
  is_finite.mk ⟨l.val.length, l.to_bijection.to_fun, l.to_bijection.is_bijective⟩

end is_finite
