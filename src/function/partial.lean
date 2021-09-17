import logic.misc
import .misc

/-!
 * Partial functions
 -/

namespace function

@[reducible,inline]
definition partial (α β : Sort _) := α → option β

reserve infixr `↝`:20
infixr ` ↝ ` := function.partial

namespace partial

--- Check if a partial function is defined at a specific point.
protected
definition is_defined_at {α β: Sort _} (f : partial α β) : α → Prop :=
  λ x, f x ≠ option.none

instance defined_decidable {α β : Sort _} {f : partial α β} : decidable_pred f.is_defined_at :=
  λ x, @option.rec_on β (λ y, f x=y → decidable (f.is_defined_at x)) (f x)
    (λ h, is_false (not_not_intro h))
    (λ b h, is_true (λ hn, option.no_confusion (h.symm.trans hn)))
    (@rfl _ (f x))

--- A partial function `f` is defined at a point `x` iff `f x = some b` for some `b`.
lemma defined_iff_some {α β : Sort _} (f : partial α β) {x : α} : f.is_defined_at x ↔ ∃ b, f x = some b :=
  begin
    split,
    show f.is_defined_at x → _, {
      intros hx,
      cases hfx : f x with b,
      case none { exfalso; exact hx hfx },
      exact ⟨b,rfl⟩
    },
    show _ → f.is_defined_at x, {
      intros hsome; cases hsome with b hb,
      intros h,
      have : some b = none,
        from hb.symm.trans h,
      injection this
    },
  end

--- Domain of partial functions.
protected
definition domain {α β : Sort _} (f : partial α β) : Sort _ :=
  subtype f.is_defined_at

--- Obtain an ordinary function by restricting the domain
protected
definition to_fun {α β : Sort _} (f : partial α β) : f.domain → β :=
  λ x, @option.rec_on β (λ y, f x.val=y → β) (f x.val)
    (false.elim ∘ x.property)
    (λ b _, b)
    rfl

--- Specify how to determine the values of the function `f.to_fun` for a partial function `f`.
protected
lemma to_fun_value_of_eq {α β : Sort _} (f : partial α β) {x : f.domain} {y : β} : f x.val = some y → f.to_fun x = y :=
  begin
    intros hxy,
    dsimp [partial.to_fun],
    calc
      @option.rec β (λ y, f x.val=y → β) (false.elim ∘ x.property) (λ b _, b) (f x.val) rfl
          = @option.rec β (λ y, f x.val=y → β) (false.elim ∘ x.property) (λ b _, b) (some y) hxy : by refine dcongr hxy (hcongr_arg _ hxy) (eq_irrel hxy).symm
      ... = y : rfl
  end

--- For each partial function `f`, the values of `f` on its domain is determined by `f.to_fun`.
protected
lemma to_fun_on_domain {α β : Sort _} {f : partial α β} {x : f.domain} : f x.val = some (f.to_fun x) :=
  begin
    cases hx : f x.val with y,
    case option.none { exact (x.property hx).elim },
    refine congr_arg some _,
    exact (f.to_fun_value_of_eq hx).symm
  end

--- Think of an ordinary function as a partial function.
protected
definition from_fun {α β : Sort _} (f : α → β) : partial α β :=
  option.some ∘ f

--- Partial functions compose.
protected
definition comp {α β γ : Sort _} : partial β γ → partial α β → partial α γ :=
  λ g f a, f a >>= g

--- Injectivity of partial maps.
protected
definition injective {α β : Sort _} (f : partial α β) : Prop :=
  ∀ x y, f.is_defined_at x → f.is_defined_at y → f x = f y → x = y

--- Surjectivity of partial maps.
protected
definition surjective {α β : Sort _} (f : partial α β) : Prop :=
  ∀ b, ∃ a, f a = option.some b

protected
lemma injective_on_domain {α : Type _} {β : Sort _} {f : partial α β} : f.injective → ∀ (x y : f.domain), f x.val = f y.val → x = y :=
  begin
    intros hinj x y hfxy,
    exact subtype.eq (hinj x.val y.val x.property y.property hfxy)
  end

--- The injectivity of a partial function `f` is equivalent to the injectivity of `f.to_fun` in the ordinary sense.
protected
lemma injective_iff {α : Type _} {β : Sort _} (f : partial α β) : f.injective ↔ injective f.to_fun :=
  begin
    split,
    show f.injective → _, {
      intros h x y,
      cases hx: f x.val with b,
      case option.none { exfalso; exact x.property hx },
      cases hy: f y.val with c,
      case option.none { exfalso; exact y.property hy },
      rw [f.to_fun_value_of_eq hx],
      rw [f.to_fun_value_of_eq hy],
      intros hbc,
      have hxy : f x.val = f y.val :=
        (hx.trans (congr_arg some hbc)).trans hy.symm,
      exact partial.injective_on_domain h x y hxy,
    },
    show _ → f.injective, {
      intros hinj x y hx hy hfxy,
      cases hfx: f x with b,
      case option.none { exact (hx hfx).elim },
      cases hfy: f y with c,
      case option.none { exact (hy hfy).elim },
      have hbc : b = c,
        by apply option.some.inj; rw [←hfx,←hfy]; exact hfxy,
      have hfxv : f.to_fun ⟨x,hx⟩ = b,
        from f.to_fun_value_of_eq hfx,
      have hfyv : f.to_fun ⟨y,hy⟩ = c,
        from f.to_fun_value_of_eq hfy,
      let hxy := hinj ((hfxv.trans hbc).trans hfyv.symm),
      exact congr_arg subtype.val hxy,
    }
  end


/-
 * Partial function that is dual to the injection from a decidable subtypes.
--/
--- Dual of the injection from a decidable subtype
definition coinj {α : Type _} (p : α → Prop) [decidable_pred p] : partial α (subtype p) :=
  λ x, dite (p x) (λ h, some ⟨x,h⟩) (λ _, none)

section coinj

variables {α : Type _} {p : α → Prop} [decidable_pred p]

--- A point belongs to the domain of `coinj p` if and only if it satisfies `p`.
lemma coinj_domain : ∀ x, (coinj p).is_defined_at x ↔ p x :=
  begin
    intros x,
    dsimp [coinj, partial.is_defined_at],
    by_cases p x,
    rw [dif_pos h]; calc
      ¬some (subtype.mk x h) = none
          ↔ true : iff_true_intro (λ h, option.no_confusion h)
      ... ↔ p x : iff.symm (iff_true_intro h),
    rw [dif_neg h]; calc
      ¬none = none
          ↔ false : ⟨false_of_ne,false.elim⟩
      ... ↔ p x : iff.symm (iff_false_intro h)
  end

--- `coinj p` is injective as a partial function.
lemma coinj_inj : (coinj p).injective :=
  begin
    intros x y hx hy hxy,
    have hpx : p x,
      from (coinj_domain x).mp hx,
    have hpy : p y,
      from (coinj_domain y).mp hy,
    dsimp [coinj] at hxy,
    rw [dif_pos hpx, dif_pos hpy] at hxy,
    exact congr_arg subtype.val (option.some.inj hxy)
  end

end coinj

end partial

end function
