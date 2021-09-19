import function.misc
import function.bijection
import data.finord
import .misc

namespace list

--- Turn a list `l` into a function from the set of members to the indices in `finord`.
protected
definition indexer {α : Type _} [decidable_eq α] (l : list α) : {x // x ∈ l} → finord l.length :=
  list.rec_on l
    (λ x, false.elim (not_mem_nil _ x.property))
    (λ a tl f x,
      dite (x.val=a) (λ _, finord.fz) $ λ h,
        finord.fs (f ⟨x.val, or.resolve_left x.property h⟩)
    )

@[simp]
protected
lemma indexer_cons_eq {α : Type _} [decidable_eq α] {a : α} {tl : list α} : ∀ {x : {x // x ∈ a :: tl}}, x.val = a → list.indexer (a :: tl) x = finord.fz :=
  begin
    intros x hx,
    cases x; dsimp * at *,
    dsimp [list.indexer]; rw [dif_pos hx]
  end

@[simp]
protected
lemma indexer_cons_neq {α : Type _} [decidable_eq α] {a : α} {tl : list α} {x : {x // x ∈ a :: tl}} (hx : x.val ≠ a) : list.indexer (a :: tl) x = finord.fs (tl.indexer ⟨x.val,or.resolve_left x.property hx⟩) :=
  begin
    cases x; dsimp * at *,
    dsimp [list.indexer]; rw [dif_neg hx]
  end

--- `l.indexer` is surjective provided `l.nodup`.
protected
lemma indexer_surjective {α : Type _} [decidable_eq α] {l : list α} : l.nodup → function.surjective l.indexer :=
  begin
    intros hnodup k,
    induction l with a tl h_ind,
    case nil { cases k },
    case cons {
      cases k with _ _ j,
      case fz {
        refine ⟨⟨a,or.inl rfl⟩,_⟩,
        dsimp [list.indexer],
        rw [dif_pos rfl]
      },
      case fs {
        cases h_ind (nodup_tail hnodup) j with x hx,
        existsi @subtype.mk α (λ x, x ∈ a :: tl) x.val (mem_cons_of_mem a x.property),
        have : x.val ≠ a, {
          intros hxa,
          cases hnodup with _ _ hatl _ _,
          exact hatl (hxa ▸ x.property)
        },
        refine eq.trans (list.indexer_cons_neq this) _,
        apply congr_arg finord.fs,
        refine eq.trans (congr_arg tl.indexer _) hx,
        exact subtype.eq rfl
      }
    }
  end

--- Convert a list `l` into a function from the set of indices of type `finord`.
protected
definition enumerator {α : Type _} : Π (l : list α), finord (length l) → α
| (x::xs) finord.fz := x
| (x::xs) (finord.fs n) := enumerator xs n

--- Every value of `l.to_fun` is a member of the original list `l`.
protected
lemma mem_of_enumerated {α : Type _} (l : list α) : ∀ x, l.enumerator x ∈ l :=
  begin
    intros x,
    induction l with a tl h_ind,
    case nil { cases x },
    case cons {
      dsimp [list.length] at x,
      cases x with _ _ x',
      case fz {
        dsimp [list.enumerator],
        exact or.inl rfl
      },
      case fs {
        dsimp [list.enumerator],
        exact or.inr (h_ind x')
      }
    }
  end

--- The same as `list.enumerator` while the codomain is restricted to the subtype of members of the given list.
protected
definition subenumerator {α : Type _} (l : list α) : finord l.length → {x  // x ∈ l} :=
  λ n, ⟨l.enumerator n, l.mem_of_enumerated _⟩

--- Every member of a list `l` appears as a value of the function `l.enumerator`.
protected
lemma enumerate_mem {α : Type _} (l : list α) {x : α} : x ∈ l → ∃ n, x = l.enumerator n :=
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

--- `l.enumerator` is an injective function provided `l.nodup`.
protected
lemma enumerator_injective {α : Type _} {l : list α} : l.nodup → function.injective l.enumerator :=
  begin
    intros hnodup x y hxy,
    induction l with a tl h_ind,
    case nil { cases x },
    cases x with _ _ x',
    case fz {
      dsimp [list.enumerator] at *,
      cases y with _ _ y',
      case fz { refl },
      case fs {
        dsimp [list.enumerator] at hxy,
        have : a ∈ tl,
          by rw [hxy]; exact tl.mem_of_enumerated y',
        exfalso,
        exact nodup_head hnodup this,
      }
    },
    case fs {
      cases y with _ _ y',
      case fz {
        dsimp [list.enumerator] at hxy,
        have : a ∈ tl,
          by rw [←hxy]; exact tl.mem_of_enumerated x',
        exfalso,
        exact nodup_head hnodup this
      },
      case fs {
        apply congr_arg finord.fs,
        dsimp [list.enumerator] at hxy,
        exact h_ind (nodup_tail hnodup) hxy,
      },
    }
  end

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

--- The value list of `l.enumerator` is exactly the original list `l`.
protected
lemma from_enumerator {α : Type _} (l : list α) : list.from_fun l.enumerator = l :=
  begin
    induction l with a tl h_ind,
    case nil { refl },
    dsimp [list.enumerator,list.from_fun] at *,
    apply congr_arg (list.cons a),
    refine eq.trans _ h_ind,
    apply list.from_fun_equiv,
    intros x,
    dsimp [list.enumerator]; refl
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



/- Composition of `l.indexer` and `l.enumerator` -/
section

variables {α : Type _} [decidable_eq α] {l : list α}

--- The members of a list can be enumerated by their indices.
@[simp]
protected
theorem enumerate_index : ∀ x, l.enumerator (l.indexer x) = x.val :=
  begin
    intros x; cases x with x hx,
    induction l with a tl h_ind,
    case nil { exfalso; exact list.not_mem_nil _ hx },
    refine dite (x=a) _ _,
    show x = a → _, {
      intros hxa,
      have : ∀ {h}, (a :: tl).indexer ⟨x,h⟩ = finord.fz,
        from λ h, list.indexer_cons_eq hxa,
      rw [this],
      dsimp [list.enumerator],
      exact hxa.symm
    },
    show x ≠ a → _, {
      intros hxa,
      have : ∀ {h}, (a :: tl).indexer ⟨x,h⟩ = finord.fs (tl.indexer ⟨x,_⟩),
        from λ h, list.indexer_cons_neq hxa,
      rw [this],
      dsimp [list.enumerator],
      exact h_ind (or.resolve_left hx hxa)
    },
  end

--- For every `l : list α`, `l.subenumerator` is always a left inverse to `l.indexer`.
@[simp]
theorem subenumerator_left_inverse_of_indexer : function.left_inverse l.subenumerator l.indexer :=
  begin
    intros x,
    dunfold list.subenumerator,
    apply subtype.eq,
    exact list.enumerate_index x
  end

--- For every `l : list α`, `l.indexer` is a left inverse to `l.subenumerator` provided `l.nodup`.
@[simp]
theorem indexer_left_inverse_of_subenumerator : l.nodup → function.left_inverse l.indexer l.subenumerator :=
  begin
    intros hnodup x,
    induction l with a tl h_ind,
    case nil { cases x },
    case cons {
      cases x with _ _ n,
      case fz {
        dsimp [list.subenumerator,list.enumerator],
        exact list.indexer_cons_eq rfl
      },
      case fs {
        dsimp [list.subenumerator,list.enumerator],
        have : tl.enumerator n ≠ a, {
          intros ha,
          exact nodup_head hnodup (ha ▸ tl.mem_of_enumerated n)
        },
        refine eq.trans (list.indexer_cons_neq this) _,
        apply congr_arg finord.fs,
        exact h_ind (list.nodup_tail hnodup) n
      }
    }
  end

end

--- For a list `l` with `l.nodup`, the index access yields a bijection between the members of `l` and the standard finite set of cardinality `l.length`.
definition enum_bijection {α : Type _} [decidable_eq α] {l : list α} (h : l.nodup): bijection (finord l.length) {x // x ∈ l} :=
{
  to_fun := l.subenumerator,
  inv := l.indexer,
  left_inverse := list.indexer_left_inverse_of_subenumerator h,
  right_inverse := list.subenumerator_left_inverse_of_indexer
}

end list
