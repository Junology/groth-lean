universes u

inductive vect (α : Type u) : ℕ → Type u
| nil {} : vect 0
| cons {n : ℕ} : α → vect n → vect (n+1)

infixr ` ∺ `:67 := vect.cons
notation `⁅`:1024 v:(foldr `, ` (h t, vect.cons h t) vect.nil `⁆`) := v

namespace vect

-- Head of a vector
attribute [reducible]
definition head {α : Type*} : Π {n : ℕ}, vect α (n+1) → α
| _ (x ∺ _) := x

-- Tail of a vector
definition tail {α : Type*} : Π {n : ℕ}, vect α (n+1) → vect α n
| _ (_ ∺ xs) := xs

--- Repeating an element
definition repeat {α : Type _} (a : α) : Π n, vect α n
| 0 := ⁅⁆
| (nat.succ n) := a ∺ (repeat n)

-- Functor
definition map {α : Type*} {β : Type*} : Π {n : ℕ}, (α → β) → vect α n → vect β n
| _ f ⁅⁆ := ⁅⁆
| _ f (x ∺ xs) := (f x) ∺ (map f xs)

--- Folding to left
definition foldl {α β : Type*} : Π {n : ℕ} (f : α → β → α), α → vect β n → α
| _ f a ⁅⁆ := a
| _ f a (x ∺ xs) := foldl f (f a x) xs

--- Folding to right
definition foldr {α β : Type*} : Π {n : ℕ} (f : α → β → β), β → vect α n → β :=
  λ n f b xs, @foldl (β → β) α _ (λ g a, f a ∘ g) id xs b

-- Zipping pairs of entries
definition zip {α : Type*} {β : Type*} : Π {n : ℕ}, vect α n → vect β n → vect (α×β) n
| _ ⁅⁆ ⁅⁆ := ⁅⁆
| _ (a ∺ as) (b ∺ bs) := (a,b) ∺ zip as bs

-- Upzipping pairs of entries
definition unzip {α : Type*} {β : Type*} : Π {n : ℕ}, vect (α×β) n → (vect α n × vect β n)
| _ ⁅⁆ := (⁅⁆, ⁅⁆)
| _ (ab ∺ abs) :=
  (ab.fst ∺ (unzip abs).fst, ab.snd ∺ (unzip abs).snd)

-- Zipping families
definition zip_fam {α : Type*} {C : α → Type*} : Π {n : ℕ}, (Π (a : α), vect (C a) n) → vect (Π (a : α), C a) n
| 0 _ := ⁅⁆
| (k+1) x := (λ a, (x a).head) ∺ zip_fam (λ a, (x a).tail)

-- Unzipping families
definition unzip_fam {α : Type*} {C : α → Type*} : Π {n : ℕ}, vect (Π a, C a) n → Π a, vect (C a) n
| _ ⁅⁆ _ := ⁅⁆
| _ (x ∺ xs) a := (x a) ∺ (unzip_fam xs a)

-- Accumulate values of functions
definition accum {α : Type*} {β : Type*} [hadd : has_add β] [defb : inhabited β] (f : α → β) : Π{n : ℕ}, vect α n → β
| _ ⁅⁆ := default β
| _ (x ∺ xs) := f x + accum xs

-- Check if an element appears in a vector
definition mem {α : Type*} : Π {n : ℕ}, vect α n → α → Prop
| _ ⁅⁆ y := false
| _ (x ∺ xs) y := (x = y) ∨ xs.mem y

-- Membership of the tail implies that on the whole vector
theorem mem_tail {α : Type*} {n : ℕ} {a : α} {xs : vect α n} : xs.mem a → ∀ {x : α}, (x ∺ xs).mem a :=
  λ h x, or.inr h

/-**************************
 -  Conversion from/to list
 -**************************-/
definition to_list {α : Type*} : Π {n : ℕ}, vect α n → list α
| _ ⁅⁆ := []
| _ (x ∺ xs) := x :: to_list xs

definition from_list {α : Type*} : Π (ls : list α), vect α (ls.length)
| [] := ⁅⁆
| (x :: xs) := x ∺ (from_list xs)


/-*********************
 -  Properties
 - *******************-/

--- `map` of `repeat` equals `repeat` of values.
theorem map_repeat {α β : Type _} {f : α → β} {a : α} : ∀ {n : ℕ}, map f (repeat a n) = repeat (f a) n
| 0 := rfl
| (n+1) := by dsimp [repeat,vect.map]; rw [map_repeat]

--- `map f` with `f` being a constant function is nothing but repeat
theorem map_const {α β : Type _} (b : β) : ∀ {n : ℕ} {as : vect α n}, map (λ _,b) as = repeat b n
| 0 ⁅⁆ := rfl
| (n+1) (a ∺ as) := by intros; dsimp [map,repeat]; rw [map_const]

-- map of compositions give rise to compositions of maps
theorem map_comp {α β γ: Type*} {f : α → β} {g : β → γ} : ∀ {n : ℕ} {t : vect α n}, map (g∘ f) t = map g (map f t)
| _ ⁅⁆ := rfl
| _ (x ∺ xs) := by unfold map; rw [map_comp]

-- map respects the identity
theorem map_id {α : Type*} : ∀ {n : ℕ} {t : vect α n}, map id t = t
| _ ⁅⁆ := rfl
| _ (x ∺ xs) := by dsimp [map,id]; rw [map_id]

-- map respects the function extensionality
theorem map_funext {α β : Type*} {f g : α → β} : (∀ a, f a = g a) → ∀ {n : ℕ} {t : vect α n}, map f t = map g t
| h _ ⁅⁆ := rfl
| h _ (x ∺ xs) := by unfold map; rw [h,map_funext h]

--- fst of unzip is map fst
theorem unzip_fst_is_map_fst {α β : Type _} : ∀ {n : ℕ} {vab : vect (α×β) n}, (unzip vab).fst = map prod.fst vab
| _ ⁅⁆ := rfl
| _ (ab ∺ abs) := by dsimp [unzip,map]; rw [unzip_fst_is_map_fst]

--- snd of unzip is map fst
theorem unzip_snd_is_map_snd {α β : Type _} : ∀ {n : ℕ} {vab : vect (α×β) n}, (unzip vab).snd = map prod.snd vab
| _ ⁅⁆ := rfl
| _ (ab ∺ abs) := by dsimp [unzip,map]; rw [unzip_snd_is_map_snd]

theorem unzip_fam_eval {α : Type _} {C : α → Type _} {a : α} : ∀ {n} {fs : vect (Π a, C a) n}, unzip_fam fs a = fs.map (λf, f a)
| _ ⁅⁆ := rfl
| _ (f ∺ fs) := by dsimp [unzip_fam,map]; rw [unzip_fam_eval]

-- vector of image is image of map
theorem image {α β : Type*} {f : α → β} : ∀ {n : ℕ} (t : vect {b // ∃ a, f a = b} n), ∃ (v : vect α n), map f v = map subtype.val t
| _ ⁅⁆ := by existsi ⁅⁆; refl
| _ (x ∺ xs) :=
  begin
    apply exists.elim x.property,
    intros a ha,
    apply exists.elim (image xs),
    intros as has,
    existsi (a ∺ as),
    unfold map,
    rw [ha,has]
  end

end vect
