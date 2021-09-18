import function.misc
import function.bijection
import data.list.misc
import data.list.map_partial
import data.finite
import data.subtype.misc
import .basic

namespace exhaustive_list

--- If `α` has an `exhaustive_list`, then each decidable subtype of `α` does.
protected
definition restrict {α : Type _} (l : exhaustive_list α) (p : α → Prop) [decidable_pred p] : exhaustive_list (subtype p) :=
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

--- Restrict an `exhaustive_list` on a subtype to a smaller subtype.
protected
definition subrestrict {α : Type _} {p q : α → Prop} [decidable_pred q] (l : exhaustive_list (subtype p)) (f : ∀ x, q x → p x) : exhaustive_list (subtype q) :=
  let l' := (l.restrict (q ∘ subtype.val)).translate bijection.subtype_uncurry.is_bijective
  in l'.translate (bijection.subtype_equiv (λ x, and_iff_right_of_imp (f x))).is_bijective

--- If two subtypes respectively admit exhaustive lists, then so does their union.
protected
definition union {α : Type _} [decidable_eq α] {p q : α → Prop} (lp : exhaustive_list (subtype p)) (lq : exhaustive_list (subtype q)) : exhaustive_list {x // p x ∨ q x} :=
  subtype.mk
    (list.union (lp.val.map subtype.inl) (lq.val.map subtype.inr)) $
    begin
      split,
      show list.nodup _, {
        apply list.nodup_union,
        exact list.nodup_map_of_nodup subtype.relax_inj lp.property.left,
        exact list.nodup_map_of_nodup subtype.relax_inj lq.property.left,
      },
      show ∀ x, x ∈ _, {
        intros x,
        apply list.mem_union_iff.mp,
        cases x.property with hx hx,
        case or.inl /- p x.val -/ {
          left,
          have : x = subtype.inl ⟨x.val,hx⟩,
            by cases x; refl,
          rw [this],
          apply list.mem_map_of_mem _ _,
          exact lp.property.right _
        },
        case or.inr /- q x.val -/ {
          right,
          have : x = subtype.inr ⟨x.val,hx⟩,
            by cases x; refl,
          rw [this],
          apply list.mem_map_of_mem _ _,
          exact lq.property.right _
        },
      },
    end

end exhaustive_list
