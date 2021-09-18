import function.misc
import data.finord
import .misc

namespace list

--- Convert a list `l` into a function from the set of indices of `l`.
protected
definition to_fun {α : Type _} : Π (l : list α), finord (length l) → α
| (x::xs) finord.fz := x
| (x::xs) (finord.fs n) := to_fun xs n

--- Conver a function out of a finite set into a list of values.
protected
definition from_fun {α : Type _} : Π {n : ℕ} (f : finord n → α), list α
| 0 _ := []
| (k+1) f := f finord.fz :: @from_fun k (f∘ finord.fs)

--- `list.from_fun` maps equivalent functions into the same list.
protected
lemma from_fun_equiv {α : Type _} {n : ℕ} : ∀ {f g : finord n → α}, (∀ x, f x = g x) → list.from_fun f = list.from_fun g :=
  begin
    induction n with n h_ind,
    case zero { intros; refl },
    case succ {
      intros f g hfg,
      dsimp [list.from_fun],
      rw [hfg],
      refine congr_arg (list.cons (g _)) (h_ind _),
      intros x,
      dsimp [function.comp],
      exact hfg _
    }
  end

--- The value list of `l.to_fun` is exactly the original list `l`.
protected
lemma from_fun_of_to {α : Type _} (l : list α) : @list.from_fun α l.length l.to_fun = l :=
  begin
    induction l with a tl h_ind,
    case nil { refl },
    dsimp [list.from_fun,list.to_fun] at *,
    apply congr_arg (list.cons a),
    exact h_ind,
  end

--- The length of the value list equals the cardinality of the domain.
protected
lemma length_of_from_fun {α : Type _} {n : ℕ} : ∀ (f : finord n → α), (list.from_fun f).length = n :=
  begin
    induction n with k h_ind,
    case zero { intros; refl },
    case succ {
      intros f,
      dsimp [list.from_fun],
      exact congr_arg nat.succ (h_ind _),
    }
  end

--- Every value of `l.to_fun` is a member of the original list `l`.
protected
lemma mem_of_to_fun_value {α : Type _} (l : list α) : ∀ x, l.to_fun x ∈ l :=
  begin
    intros x,
    induction l with a tl h_ind,
    case nil { cases x },
    case cons {
      dsimp [list.length] at x,
      cases x with _ _ x',
      case fz {
        dsimp [list.to_fun],
        exact or.inl rfl
      },
      case fs {
        dsimp [list.to_fun],
        exact or.inr (h_ind x')
      }
    }
  end

--- Every member of a list `l` appears as a value of the function `l.to_fun`.
protected
lemma to_fun_value_of_mem {α : Type _} (l : list α) {x : α} : x ∈ l → ∃ n, x = l.to_fun n :=
  begin
    intros hx,
    induction l with a tl h_ind,
    case nil { exfalso; exact not_mem_nil _ hx },
    case cons {
      cases hx,
      case or.inl { exact ⟨finord.fz, hx⟩ },
      case or.inr {
        cases h_ind hx with n hn,
        exact ⟨n.fs, hn⟩,
      }
    }
  end

--- `l.nodup` implies that `l.to_fun` is an injective function.
protected
lemma to_fun_injective_of_nodup {α : Type _} {l : list α} : l.nodup → function.injective l.to_fun :=
  begin
    intros hnodup x y hxy,
    induction l with a tl h_ind,
    case nil { cases x },
    cases x with _ _ x',
    case fz {
      dsimp [list.to_fun] at *,
      cases y with _ _ y',
      case fz { refl },
      case fs {
        dsimp [list.to_fun] at hxy,
        have : a ∈ tl,
          by rw [hxy]; exact tl.mem_of_to_fun_value y',
        exfalso,
        exact nodup_head hnodup this,
      }
    },
    case fs {
      cases y with _ _ y',
      case fz {
        dsimp [list.to_fun] at hxy,
        have : a ∈ tl,
          by rw [←hxy]; exact tl.mem_of_to_fun_value x',
        exfalso,
        exact nodup_head hnodup this
      },
      case fs {
        apply congr_arg finord.fs,
        dsimp [list.to_fun] at hxy,
        exact h_ind (nodup_tail hnodup) hxy,
      },
    }
  end

end list
