import function.misc
import function.bijection
import data.list.misc
import data.list.finord
import .finord

--- Class for types that are isomorphic to `finord n` for some `n`.
class is_finite (α : Type _) : Prop :=
  (isom_to_finord : ∃ (n : ℕ), nonempty (bijection α (finord n)))

@[reducible,inline]
definition isom_to_finord (α : Type _) [is_finite α] : ∃ (n : ℕ), nonempty (bijection α (finord n)) :=
  is_finite.isom_to_finord

namespace is_finite

variables {α : Type _} [is_finite α]

#check @is_finite.rec

lemma replace_finord {motive : ℕ → Prop} : (∀ n, finord n → motive n) → α → ∃ n, motive n :=
  begin
    intros h a,
    cases _root_.isom_to_finord α with n e_f,
    cases e_f with f,
    exact ⟨n, h n (f.to_fun a)⟩
  end

--- Every finite type admits a complete list of elements.
lemma has_element_list : nonempty {l : list α // l.nodup ∧ ∀ (x : α), x ∈ l} :=
  begin
    cases _root_.isom_to_finord α with n e_f,
    cases e_f with f,
    constructor,
    existsi (finord.elem_list n).map f.inv,
    split,
    show list.nodup _, {
      refine list.nodup_map_of_nodup _ _,
      exact (function.has_inverse.bijective f.inv_has_inverse).left,
      exact finord.elem_list_nodup n
    },
    show ∀ (x : α), x ∈ list.map f.inv (finord.elem_list n), {
      intros x,
      suffices : f.to_fun x ∈ finord.elem_list n, {
        have : f.inv (f.to_fun x) ∈ (finord.elem_list n).map f.inv,
          from list.mem_map_of_mem _ _ this,
        rw [f.left_inverse] at this,
        assumption
      },
      exact finord.elem_list_complete _
    }
  end

#print axioms has_element_list

end is_finite
