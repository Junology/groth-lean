import .misc
import function.partial

/-!
 * Analogue of `list.map` for partial functions.
--/

namespace list

--- Analogue of `map` for partial functions.
@[reducible]
definition map_partial {α β : Type _} (f : α ↝ β) (l : list α) : list β :=
  list.rec_on l [] $
    λ a tl ind,
      option.rec_on (f a) ind (λ b, b :: ind)

@[simp]
lemma map_partial_nil {α β : Type _} {f : α ↝ β} : map_partial f [] = [] := rfl

@[simp]
lemma map_partial_cons {α β : Type _} {f : α ↝ β} {a : α} {tl : list α} : map_partial f (a::tl) = option.rec_on (f a) (map_partial f tl) (λ b, b :: map_partial f tl) := rfl

--- `filter` with values in subtypes
@[reducible,inline]
definition filter_to_subtype {α : Sort _} (p : α → Prop) [decidable_pred p] (l : list α) : list (subtype p) :=
  l.map_partial (function.partial.coinj p)

--- Partial maps respect the membership relation on the domain.
lemma mem_map_partial_of_mem {α β : Type _} {f : α ↝ β} : ∀ (x : f.domain) (l : list α), x.val ∈ l → f.to_fun x ∈ l.map_partial f :=
  begin
    intros x l hx,
    induction l with a tl h_ind,
    case nil { exfalso; exact not_mem_nil _ hx },
    /- ↓ induction step: l = a::tl ↓ -/
    rw [map_partial_cons],
    cases hfa : f a with b,
    case none {
      dsimp *,
      cases hx,
      case or.inl { exfalso; exact x.property ((congr_arg f hx).trans hfa) },
      case or.inr { exact h_ind hx }
    },
    case some {
      dsimp *,
      cases hx,
      case or.inl {
        suffices : f.to_fun x = b,
          from or.inl this,
        apply function.partial.to_fun_value_of_eq,
        calc
          f x.val = f a : congr_arg f hx
          ...     = some b : hfa
      },
      case or.inr { right; exact h_ind hx },
    }
  end

--- Injective partial maps reflect the membership relation.
lemma mem_of_mem_map_partial {α β : Type _} {f : α ↝ β} : f.injective → ∀ (x : f.domain) (l : list α), f.to_fun x ∈ l.map_partial f → x.val ∈ l :=
  begin
    intros hinj x l hfmem,
    induction l with a tl h_ind,
    case nil { exfalso; exact not_mem_nil _ hfmem },
    case cons {
      cases hfa : f a with b hb,
      case none {
        rw [map_partial_cons, hfa] at hfmem,
        dsimp * at hfmem,
        exact or.inr (h_ind hfmem)
      },
      case some {
        rw [map_partial_cons, hfa] at hfmem,
        dsimp * at hfmem,
        cases hfmem,
        case or.inl {
          left,
          have : f x.val = f a,
            calc
              f x.val
                  = some (f.to_fun x) : function.partial.to_fun_on_domain
              ... = some b : by rw [hfmem]
              ... = f a : hfa.symm,
          exact hinj _ _ x.property (f.defined_iff_some.mpr ⟨b,hfa⟩) this,
        },
        case or.inr { exact or.inr (h_ind hfmem) }
      }
    }
  end

--- `map_partial` with injective partial maps respect `list.nodup`.
lemma nodup_map_partial_of_nodup {α β : Type _} {f : α ↝ β} {l : list α} : f.injective → l.nodup → (l.map_partial f).nodup :=
  begin
    intros hinj hnodup,
    induction l with a tl h_ind,
    case nil { exact nodup.nil },
    rw [map_partial_cons],
    cases hfa: f a with b,
    case none { exact h_ind (nodup_tail hnodup) },
    case some {
      dsimp *,
      refine nodup.cons _ (h_ind (nodup_tail hnodup)),
      let x : f.domain := ⟨a, f.defined_iff_some.mpr ⟨b,hfa⟩⟩,
      have : f.to_fun x = b,
        from f.to_fun_value_of_eq hfa,
      rw [←this],
      apply mt (mem_of_mem_map_partial hinj x tl),
      cases hnodup with _ _ h _; exact h
    }
  end

end list
