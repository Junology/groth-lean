import logic.spaceship
import logic.funrel

--- Inductively defined finite sets
inductive finord : ℕ → Type
  | fz {n : ℕ} : finord (n+1)
  | fs {n : ℕ} : finord n → finord (n+1)

--- finord has a decidable equality
instance {n : ℕ} : decidable_eq (finord n) :=
  begin
    simp [decidable_eq, decidable_rel],
    intros a b,
    induction a with m m a ha,
    all_goals {
      cases b with n n b,
      try { exact decidable.is_true rfl },
      try { exact decidable.is_false (not.intro (λ h, finord.no_confusion h)) }
    },
    cases ha b,
    case decidable.is_false {
      apply decidable.is_false,
      apply not.intro,
      intros hyp,
      have : a = b, by injection hyp,
      contradiction
    },
    case decidable.is_true {
      rw h,
      exact decidable.is_true rfl
    }
  end

namespace finord

--- finord 0 is empty
lemma zero_empty : finord 0 → false := by intros k; cases k

--- Injectivity of the constructors
lemma fz_not_fs {n : ℕ} : ∀ {k : finord n}, fs k ≠ fz :=
  begin
    intros k hk,
    injection hk
  end

--- `fs` is injective.
lemma fs_inj {n : ℕ} : function.injective (@finord.fs n) :=
  begin
    intros k l h,
    injection h
  end

--- Strict comparison on finite ordinals
attribute [reducible]
protected
definition lt : ∀ {n}, finord n → finord n → Prop
| _ _ fz := false
| _ fz (fs _) := true
| _ (fs i) (fs j) := lt i j

instance {n} : has_lt (finord n) :=
  has_lt.mk (@finord.lt n)

--- The standard strict orders on finite ordinals are decidable.
protected
lemma lt_decidable : ∀ {n}, decidable_rel (@finord.lt n)
| _ i fz := by cases i; exact is_false false.elim
| _ fz (fs _) := is_true true.intro
| _ (fs i) (fs j) := lt_decidable i j

--- The standard strict orders on finite ordinals are irreflexive.
protected
lemma lt_irrefl {n} : ∀ (i : finord n), ¬ i.lt i :=
  begin
    intros i,
    induction i with n' n' i hi,
    case finord.fz { simp [finord.lt] },
    case finord.fs {
      simp [finord.lt],
      exact hi
    }
  end

--- The standard strict orders on finite ordinals are asymmetric.
protected
lemma lt_asymm {n} : ∀ {i j : finord n}, i.lt j → ¬ j.lt i :=
  begin
    intros i j hab,
    induction i with _ n' i hi,
    case finord.fz {
      cases j; exact false.elim
    },
    case finord.fs {
      cases j with j' _ j',
      case finord.fz {
        simp [finord.lt] at hab,
        contradiction
      },
      case finord.fs {
        unfold finord.lt,
        unfold finord.lt at hab,
        exact hi hab
      }
    }
  end

--- With respect to the standard strict orders on finite ordinals, incomparability implies equality.
protected
lemma lt_incomp_eq {n} : ∀ {i j : finord n}, ¬ i.lt j → ¬ j.lt i → i=j :=
  begin
    intros i j hij hji,
    induction i with n' n' i hi_ind,
    case finord.fz {
      cases j with _ _ j',
      case finord.fz { trivial },
      case finord.fs {
        simp [finord.lt] at hji,
        contradiction
      }
    },
    case finord.fs {
      cases j with _ _ j',
      case finord.fz { simp [finord.lt] at hij; contradiction },
      case finord.fs {
        simp *,
        unfold finord.lt at hij hji,
        exact hi_ind hij hji
      }
    }
  end

--- The standard strict orders on finite ordinals are transitive.
attribute [trans]
protected
lemma lt_trans {n} : ∀ {i j k : finord n}, i.lt j → j.lt k → i.lt k :=
  begin
    intros i j k hij hjk,
    induction k with n' n' k hk_ind,
    case finord.fz { cases j; simp [finord.lt] at hjk; contradiction },
    -- In the following, we may assume `k = fs _`
    cases i with n' n' i',
    case finord.fz { unfold finord.lt },
    case finord.fs {
      cases j with n' n' j',
      case finord.fz { unfold finord.lt at *; contradiction },
      case finord.fs { unfold finord.lt at *; exact hk_ind hij hjk }
    }
  end

--- The standard strict orders on finite ordinals are transitive.
protected
lemma lt_trichotomous {n} : ∀ {i j : finord n}, i.lt j ∨ i=j ∨ j.lt i :=
  begin
    intros i j,
    induction i with n' n' i' hi_ind,
    case finord.fz {
      cases j with _ _ j',
      case finord.fz { right; left; refl },
      case finord.fs { left; simp [finord.lt] }
    },
    case finord.fs {
      cases j with _ _ j',
      case finord.fz { right; right; simp [finord.lt] },
      case finord.fs { simp [finord.lt]; exact hi_ind }
    }
  end

instance {n} : is_irrefl (finord n) finord.lt :=
  is_irrefl.mk (@finord.lt_irrefl n)
instance {n} : is_asymm (finord n) finord.lt :=
  is_asymm.mk (@finord.lt_asymm n)
instance {n} : is_trans (finord n) finord.lt :=
  is_trans.mk (@finord.lt_trans n)
instance {n} : is_strict_order (finord n) finord.lt :=
  { /- auto-generated -/ }
instance {n} : is_incomp_trans (finord n) finord.lt :=
  begin
    constructor,
    intros i j k hij hjk,
    have : i=k,
      by calc
        i = j : finord.lt_incomp_eq hij.left hij.right
        ... = k : finord.lt_incomp_eq hjk.left hjk.right,
    rw [this],
    split; exact finord.lt_irrefl k
  end
instance {n} : is_strict_weak_order (finord n) finord.lt :=
  { /- auto-generated -/ }
instance {n} : is_trichotomous (finord n) finord.lt :=
  is_trichotomous.mk (@finord.lt_trichotomous n)
instance {n} : is_strict_total_order (finord n) finord.lt :=
  { /- auto-generated -/ }

--- Injection into the successor ordinal that preserves element representation; e.g. fz ↦ fz and fs n ↦ fs n
definition inject_succ : Π {m}, finord m → finord m.succ
| _ fz := fz
| _ (fs k) := fs (inject_succ k)

--- Iterated version of injection
definition inject {m : ℕ} : Π (k : ℕ), finord m → finord (m+k)
| 0 := id
| 1 := inject_succ -- this assures the definitional equality inject 1 = inject_succ
| (k+2) := inject_succ ∘ inject (k+1)

--- Convert into fin
definition to_fin : Π {n : ℕ}, finord n → fin n
| 0 k := (zero_empty k).elim
| (n+1) fz := ⟨0,nat.zero_lt_succ n⟩
| (n+1) (fs k) := (to_fin k).succ

--- to_fin transforms finord.fs into fin.succ
theorem to_fs_succ : ∀ {n : ℕ} (k : finord n), to_fin k.fs = (to_fin k).succ :=
  begin
    intros,
    cases k with k n k,
    case finord.fz {
      simp [to_fin]
    },
    case finord.fs {
      unfold to_fin
    }
  end

--- Convert from fin
definition from_fin : Π {n : ℕ}, fin n → finord n
| 0 ⟨k,hk⟩ := (nat.not_lt_zero k hk).elim
| (n+1) ⟨0,_⟩ := fz
| (n+1) ⟨k+1,hk⟩ := fs (from_fin ⟨k, nat.lt_of_add_lt_add_right hk⟩)

--- from_fin transforms fin.succ into finord.fs
theorem from_succ_fs : ∀ {n : ℕ} (k : fin n), from_fin k.succ = (from_fin k).fs :=
  begin
    intros n k,
    cases k with kv hkv,
    simp [fin.succ,from_fin],
  end

theorem fromto_id {n : ℕ} (k : finord n) : from_fin (to_fin k) = k :=
  begin
    induction n with n hind,
    case nat.zero {
      cases k,
    },
    case nat.succ {
      cases k with _ _ k,
      case finord.fz {
        simp [finord.to_fin, finord.from_fin]
      },
      case finord.fs {
        simp [finord.to_fin],
        by calc
          from_fin k.to_fin.succ
              = (from_fin k.to_fin).fs : from_succ_fs _
          ... = k.fs : by rw [hind k]
      }
    }
  end

theorem tofrom_id {n : ℕ} (k : fin n) : to_fin (from_fin k) = k :=
  begin
    cases k with kv hkv,
    apply subtype.eq; simp [subtype.val],
    revert kv hkv,
    induction n with n hind; intros,
    case nat.zero {
      exact (nat.not_lt_zero kv hkv).elim
    },
    case nat.succ {
      cases kv with kv,
      case nat.zero {
        simp [from_fin, to_fin, subtype.val],
      },
      case nat.succ {
        simp [from_fin, to_fin],
        have : ∀ (m : fin n), m.succ.val = m.val.succ :=
          by intros; cases m; trivial,
        rw [this],
        suffices : (from_fin ⟨kv, _⟩).to_fin.val = kv,
          by rw [this],
        apply hind
      }
    }
  end

--- The number of elements that satisfy a decidable predicator
definition card_of : Π {n : ℕ} (p : finord n → Prop) [decidable_pred p], ℕ
| 0 _ _ := 0
| (k+1) p h :=
  let i := @card_of k (p ∘ finord.fs) (λ x, h (fs x))
  in @ite _ (p finord.fz) (h _) (1+i) i

end finord
