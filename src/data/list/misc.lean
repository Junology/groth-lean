import logic.misc

namespace list

open list

/-!
 * Lemmas around `list.mem`.
--/

--- `propext` free version of list.mem_append
@[simp]
lemma mem_append' {α : Sort _} {a : α} {s t : list α} : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t :=
  begin
    induction s with x xs h_ind,
    case list.nil {
      by calc
        a ∈ nil ++ t
            ↔ a ∈ t : by rw [list.nil_append]
        ... ↔ (a ∈ nil) ∨ a∈ t : iff.symm (or_disproof_left (not_mem_nil a))
    },
    case list.cons {
      dsimp [mem_cons_eq],
      by calc
        a = x ∨ a ∈ xs ++ t
            ↔ a = x ∨ a ∈ xs ∨ a ∈ t : or_congr (iff.refl (a=x)) h_ind
        ... ↔ (a = x ∨ a ∈ xs) ∨ a ∈ t : iff.symm (or_assoc _ _)
    }
  end

--- Membership relation in a list after `list.filter`.
lemma mem_filter {α : Sort _} {as : list α} {p : α → Prop} [decidable_pred p] : ∀ a, a ∈ as.filter p ↔ (a ∈ as ∧ p a) :=
  begin
    intros x,
    induction as with a as h_ind,
    case list.nil {
      dunfold filter,
      by calc
        x ∈ []
            ↔ false : mem_nil_iff x
        ... ↔ false ∧ p x : iff.symm (false_and _)
        ... ↔ (x ∈ []) ∧ p x
              : and_congr (iff.symm (mem_nil_iff _)) (iff.refl _)
    },
    case list.cons {
      dunfold filter,
      by_cases p a,
      focus /- CASE: p a -/ {
        rw [ite_eval_true h],
        dsimp [mem_cons_eq],
        by calc
          x = a ∨ x ∈ as.filter p
              ↔ (x = a ∧ p x) ∨ (x ∈ as ∧ p x)
                : or_congr (iff.symm ∘ and_iff_left_of_imp $ by intro hx; rw [hx]; assumption) h_ind
          ... ↔ (x = a ∨ x ∈ as) ∧ p x : iff.symm or_and_distrib
      },
      focus /- CASE: ¬p a -/ {
        rw [ite_eval_false h],
        dsimp [mem_cons_eq],
        have : ¬(x = a ∧ p x), {
          intros hx,
          rw [←hx.left] at h,
          exact h hx.right
        },
        by calc
          x ∈ filter p as
              ↔ x ∈ as ∧ p x : h_ind
          ... ↔ _ : iff.symm (or_false _)
          ... ↔ false ∨ (x ∈ as ∧ p x) : or.comm
          ... ↔ (x = a ∧ p x) ∨ (x ∈ as ∧ p x) : or_congr (iff.symm (iff_false_intro this)) (iff.refl _)
          ... ↔ (x = a ∨ x ∈ as) ∧ p x : iff.symm or_and_distrib
      }
    }
  end

--- `map f` respects the membership relation.
lemma mem_map_of_mem {α β : Type _} {f : α → β} : ∀ (x : α) (l : list α), x ∈ l → f x ∈ l.map f
| x [] h := false.elim $ not_mem_nil x h
| x (a::tl) h :=
  or.elim h
    (λ ha, or.inl (congr rfl ha))
    (λ htl, or.inr (mem_map_of_mem x tl htl))

--- `map f` reflects the membership relation provided `f` is injective.
lemma mem_of_mem_map {α β : Type _} {f : α → β} : function.injective f → ∀ (x : α) (l : list α), f x ∈ l.map f → x ∈ l :=
  begin
    intros hf x l hfx,
    induction l with a tl h_ind,
    case nil { exact (not_mem_nil x hfx).elim },
    case cons {
      exact or.elim hfx (λ h, or.inl (hf h)) (λ h, mem_cons_of_mem _ (h_ind h))
    }
  end

--- If `y` lies outside of the image of a function `f`, then it cannot be a member of any lists of the form `map f l`.
lemma not_mem_map_of_offimage {α β : Type _} {f : α → β} (y : β) : (∀ x, f x ≠ y) → ∀ {l : list α}, y ∉ l.map f
| _ [] := not_mem_nil y
| hy (a::as) :=
  λ h, or.elim h (λ h, hy a h.symm) (not_mem_map_of_offimage hy)

--- If `list` has no member, then it is `nil`.
lemma is_nil_of_no_mem {α : Sort _} : ∀ {l : list α}, (∀ x, x ∉ l) → l = []
| [] _ := rfl
| (a::as) h := false.elim (h a (mem_cons_self a as))

--- Every member of `list.filter p l` should be a member of `l`.
lemma not_mem_filter {α : Sort _} {as : list α} {p : α → Prop} [decidable_pred p] : ∀ a, a ∉ as → a ∉ as.filter p :=
  begin
    intros a ha hfilt,
    exact ha ((mem_filter a).mp hfilt).left
  end

--- Any subset of `list.nil` is itself `list.nil`.
lemma subset_nil {α : Sort _} {l : list α} : l.subset [] → l = [] :=
  begin
    cases l with a as,
    case nil {
      intros; refl
    },
    case cons {
      intros hsub,
      have : a ∈ [], from hsub (or.inl rfl),
      exfalso; exact not_mem_nil a this
    },
  end


/-!
 * No duplicates; based on `list.nodup` in `mathlib`.
--/

--- Guarantees that each entry in a list appears at most once.
inductive nodup {α : Sort _} : list α → Prop
| nil : nodup []
| cons : ∀ {a : α} {l : list α}, (a ∉ l) → nodup l → nodup (a :: l)

lemma nodup_head {α : Sort _} {a : α} {l : list α} : (a :: l).nodup → a ∉ l :=
  λ h, by cases h; assumption

lemma nodup_tail {α : Sort _} {a : α} {l : list α} : (a :: l).nodup → l.nodup :=
  λ h, by cases h; assumption

lemma nodup_tail_of_sub {α : Sort _} {a : α} {l₁ l₂ : list α} : (a::l₁).nodup → (a::l₁ ⊆ a::l₂) → (l₁ ⊆ l₂) :=
  begin
    intros hnodup₁ h x hx,
    cases h (mem_cons_of_mem _ hx) with hxa hxl₂,
    case or.inl /- x = a -/ {
      cases hnodup₁ with _ _ hal₁ _,
      exact false.elim (hal₁ (hxa▸hx)),
    },
    case or.inr /- x ∈ l₂ -/ {
      exact hxl₂
    }
  end

--- `l.nodup` implise `(l.filter p).nodup` for any decidable predicator `p`.
lemma nodup_filter {α : Sort _} {p : α → Prop} [decidable_pred p] : ∀ {l}, nodup l → nodup (l.filter p)
| _ nodup.nil := nodup.nil
|(a :: as) (nodup.cons ha has) :=
  begin
    dunfold filter,
    by_cases (p a),
    focus /- p a -/ {
      rw [ite_eval_true h],
      exact nodup.cons (not_mem_filter a ha) (nodup_filter has),
    },
    focus /- ¬p a -/ {
      rw [ite_eval_false h],
      exact nodup_filter has
    }
  end

--- `map f` reflects `nodup`.
lemma nodup_of_nodup_map {α β : Type _} {f : α → β} : ∀ {l : list α}, nodup (l.map f) → nodup l
| [] _ := nodup.nil
| (a::tl) hfnodup :=
  begin
    refine nodup.cons _ (nodup_of_nodup_map (nodup_tail hfnodup)),
    dsimp [map] at hfnodup,
    cases hfnodup with _ _ hfatl _,
    exact mt (mem_map_of_mem a tl) hfatl
  end

--- `map f` respects `nodup`.
lemma nodup_map_of_nodup {α β : Type _} {f : α → β} : function.injective f → ∀ {l}, nodup l → nodup (l.map f)
| _ [] _ := nodup.nil
| hf (a::tl) hnodup :=
  begin
    refine nodup.cons _ (nodup_map_of_nodup hf (nodup_tail hnodup)),
    cases hnodup with _ _ hatl _,
    intros hfatl,
    exact hatl (mem_of_mem_map hf _ _ hfatl)
  end


/-!
 * Permutation on lists; based on `list.perm` in `mathlib`.
--/

inductive perm {α : Sort _} : list α → list α → Prop
| nil {} : perm [] []
| cons {a : α} {l₁ l₂ : list α} : perm l₁ l₂ → perm (a::l₁) (a::l₂)
| head {a b : α} {l : list α} : perm (a :: b :: l) (b :: a :: l)
| trans {l₁ l₂ l₃ : list α} : perm l₂ l₃ → perm l₁ l₂ → perm l₁ l₃

attribute [trans] perm.trans

namespace perm

@[refl]
protected
lemma rfl {α : Sort _} : ∀ (l : list α), perm l l
| [] := perm.nil
| (a::as) := perm.cons (rfl as)

@[symm]
protected
lemma symm {α : Sort _} {l₁ l₂ : list α} (hperm : perm l₁ l₂) : perm l₂ l₁ :=
  @perm.rec_on α (λ l₁ l₂, perm l₂ l₁) l₁ l₂ hperm
    perm.nil
    (λ _ _ _ _ h, perm.cons h)
    (λ _ _ _ , perm.head)
    (λ l₁ l₂ l₃ _ _ h₂ h₁, perm.trans h₁ h₂)

--- `perm l₁ l₂` implies that `l₂` contains `l₁`.
protected
lemma subset {α : Sort _} {l₁ l₂ : list α} (hperm : perm l₁ l₂) : l₁.subset l₂ :=
  @perm.rec_on α (λ l₁ l₂, ∀ a, a ∈ l₁ → a ∈ l₂) l₁ l₂ hperm
    /- perm.nil -/ (λ _, id)
    /- perm.cons -/ (
      λ _ l₁ l₂ _ h_ind a hl₁, or.imp_right (h_ind a) hl₁
    )
    /- perm.head -/ (
      λ a b l x h_ind,
        or.assoc.mp ((or_congr or.comm (iff.refl _)).mpr (or.assoc.mpr h_ind))
    )
    /- perm.trans -/ (
      λ l₁ l₂ l₃ _ _ hleft hright a, hleft a ∘ hright a
    )

protected
lemma mem_iff {α : Sort _} {l₁ l₂ : list α} (hperm : perm l₁ l₂) : ∀ a, a ∈ l₁ ↔ a ∈ l₂ :=
  λ _, ⟨λ h, hperm.subset h, λ h, hperm.symm.subset h⟩

--- `perm` implies an implication of "non-membership" relation.
protected
lemma not_mem {α : Sort _} {l₁ l₂ : list α} (hperm : perm l₁ l₂) : ∀ a, a ∉ l₁ → a ∉ l₂ :=
  λ _ hl₁ hl₂, hl₁ (perm.subset hperm.symm hl₂)

end perm

--- Membership relation `x ∈ l` is equivalent to `perm` with a list that has `x` as a head.
lemma mem_perm_head {α : Sort _} {a : α} {l : list α} : (a ∈ l) ↔ (∃ l', perm l (a::l')) :=
  begin
    split,
    show a ∈ l → _, {
      induction l with b bs h_ind,
      case list.nil {
        exact false.elim ∘ (mem_nil_iff a).mp
      },
      intros ha,
      rw [mem_cons_eq] at ha,
      cases ha,
      case or.inl { rw [ha]; exact ⟨bs,perm.rfl _⟩ },
      case or.inr {
        cases h_ind ha with l'' hperm,
        existsi b::l'',
        exact perm.trans perm.head (perm.cons hperm)
      }
    },
    show _ → a ∈ l, {
      intros hhead,
      cases hhead with l' hperm,
      exact hperm.symm.subset (or.inl rfl)
    }
  end

lemma perm_nodup {α : Sort _} {l₁ l₂ : list α} (hperm : perm l₁ l₂) : l₁.nodup → l₂.nodup :=
  @perm.rec_on α (λ l₁ l₂, l₁.nodup → l₂.nodup) l₁ l₂ hperm
    /- nodup.nil -/ id
    /- nodup.cons -/ (
      λ a lt₁ lt₂ htperm h_ind hlt₁,
        nodup.cons
          (perm.not_mem htperm a (nodup_head hlt₁))
          (h_ind (nodup_tail hlt₁))
    )
    /- nodup.head -/ (
      λ a b lt h_ind,
        begin
          cases h_ind with _ _ hhead h_ind; cases h_ind with _ _ hhead' h_ind,
          constructor,
          show b ∉ a :: lt, {
            intros hb,
            exact hb.elim (λ h, hhead (or.inl h.symm)) (λ h, hhead' h)
          },
          show (a :: lt).nodup, {
            exact nodup.cons (mt or.inr hhead) h_ind,
          }
        end
    )
    /- nodup.trans -/ (
      λ _ _ _ _ _ h₂ h₁, h₂ ∘ h₁
    )

--- `perm l₁ l₂` is derived from the equivalence of the membership relations provided both `l₁` and `l₂` are `list.nodup`.
theorem nodup_perm_of_mem {α : Sort _} {l₁ l₂ : list α} : l₁.nodup → l₂.nodup → (∀ x, x ∈ l₁ ↔ x ∈ l₂) → perm l₁ l₂ :=
  begin
    intros hnodup₁ hnodup₂ hiff,
    revert l₂,
    induction l₁ with a tl₁ h_ind,
    case list.nil {
      intros _ _ hiff,
      rw [is_nil_of_no_mem (λ x, not_mem_nil x ∘ (hiff x).mpr)]
    },
    case list.cons {
      intros l₂ hnodup₂ hiff,
      have : a ∈ l₂ := (hiff a).mp (mem_cons_self _ _),
      cases mem_perm_head.mp this with l' hperm,
      refine perm.trans hperm.symm (perm.cons _),
      apply h_ind (nodup_tail hnodup₁) (nodup_tail $ perm_nodup hperm hnodup₂),
      intros x,
      split,
      show x ∈ tl₁ → x ∈ l', {
        suffices : a::tl₁ ⊆ a::l', {
          apply nodup_tail_of_sub hnodup₁ this,
        },
        calc
          a::tl₁ ⊆ l₂ : λ y, (hiff y).mp
          ...    ⊆ a::l' : hperm.subset
      },
      show x ∈ l' → x ∈ tl₁, {
        suffices : a::l' ⊆ a::tl₁, {
          apply nodup_tail_of_sub (perm_nodup hperm hnodup₂) this,
        },
        calc
          a::l' ⊆ l₂ : hperm.symm.subset
          ...   ⊆ a::tl₁ : λ y, (hiff y).mpr
      }
    }
  end

end list
