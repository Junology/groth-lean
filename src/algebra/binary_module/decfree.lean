import data.bool.misc
import data.list.misc
import logic.misc
import logic.finite
import .basic .hom .bool

namespace binary_module

open binary_module

local attribute [instance] binary_abelian

@[reducible]
protected
definition has_finite_support (α : Type _) [decidable_eq α] (φ : Type _) [decidable_eq φ] [model binary_module φ] : inv_pred binary_module (α → φ) :=
{
  p := λ f, is_finite {x // f x ≠ 0},
  hinv :=
    begin
      intros n μ fs hall,
      cases μ,
      case ops.zero {
        cases fs,
        apply is_finite.of_empty,
        intros x,
        exact not_not_intro rfl
      },
      case ops.add {
        cases fs with _ f fs; cases fs with _ g gs; cases gs,
        dsimp [vect.is_all] at hall,
        let hfin := hall.left.of_union hall.right.left,
        let hfin' := hfin.of_subrestrict (λ x, f x + g x ≠ 0),
        dsimp at hfin',
        refine is_finite.of_iff _ hfin',
        intros x,
        have : @premodel.act binary_module _ _ _ ops.add ⁅f,g⁆ x = f x + g x,
          by refl,
        rw [this],
        split,
        exact and.right,
        intros hfgx,
        split; try { assumption },
        refine dite (f x = 0) _ _,
        show f x = 0 → _, {
          intros hfx,
          rw [hfx, _root_.zero_add] at hfgx,
          exact or.inr hfgx
        },
        show f x ≠ 0 → _, {
          exact or.inl
        }
      }
    end
}

@[reducible]
definition finsupp_fun (α : Type _) [decidable_eq α] (φ : Type _) [decidable_eq φ] [model binary_module φ] :=
  submodel binary_module (binary_module.has_finite_support α φ)

@[reducible,inline]
definition finsupp_bits (α : Type _) [decidable_eq α] :=
  finsupp_fun α bool

@[reducible]
definition singlebit {α : Type _} [decidable_eq α] : α → finsupp_bits α :=
  λ a, subtype.mk (λ x, to_bool (a=x)) $
    begin
      dunfold binary_module.has_finite_support,
      dsimp *,
      apply is_finite.of_exhaustive_list,
      have ha : to_bool (a = a) ≠ 0,
        by rw [to_bool_tt rfl]; intro h; exact bool.ff_ne_tt h.symm,
      refine subtype.mk [⟨a,ha⟩] ⟨list.nodup.nil.cons (list.not_mem_nil _), _⟩,
      intros x,
      refine dite (a = x.val) _ _,
      show a = x.val → _, {
        intros hax,
        exact or.inl (subtype.eq hax.symm)
      },
      show a ≠ x.val → _, {
        intros hax,
        have : ff ≠ 0,
          by let h := x.property; rw [to_bool_ff hax] at h; exact h,
        exact false.elim (this rfl)
      }
    end

--- The functional relation that represents the accumuration of a `binary_module`-valued function with boolean weights.
definition waccum_funrel {α : Type _} [decidable_eq α] {φ : Type _} [model binary_module φ] (f : α → φ) : finsupp_bits α ⇒ φ :=
{
  p := λ w y, ∀ (l : exhaustive_list {a // w.val a ≠ 0}), accum f l.underlying = y,
  huniq :=
    begin
      intros w; cases w,
      dunfold binary_module.has_finite_support at w_property,
      dsimp * at w_property,
      cases @is_finite.has_exhaustive_list _ w_property with l,
      existsi accum f l.underlying,
      dsimp *,
      split,
      show ∀ (l' : exhaustive_list _), accum f l'.underlying = accum f l.underlying, {
        intros l',
        exact accum_perm (l'.underlying_perm l)
      },
      show ∀ y h, y = _, {
        intros y h; rw [h]
      }
    end
}

--- `waccum` with zero weight equals zero.
lemma waccum_funrel_zero {α : Type _} [decidable_eq α] {φ : Type _} [model binary_module φ] (f : α → φ) : (waccum_funrel f).p (binary_module.zero _) 0 :=
  begin
    dsimp [waccum_funrel],
    intros l,
    suffices : l.underlying = [], {
      rw [this]; exact accum_nil
    },
    refine l.of_empty_underlying _,
    intros x,
    apply not_not_intro,
    refl
  end

--- `waccum` respects the addition of weights.
lemma waccum_funrel_add {α : Type _} [decidable_eq α] {φ : Type _} [model binary_module φ] (f : α → φ) : ∀ (v w : finsupp_bits α) (y z : φ), (waccum_funrel f).p v y → (waccum_funrel f).p w z → (waccum_funrel f).p (binary_module.add v w) (y+z) :=
  begin
    dsimp [waccum_funrel],
    intros v w y z hvy hwz l,
    have : ∀ a, (binary_module.add v w).val a ≠ 0 ↔ (v.val a ≠ 0 ∧ ¬w.val a ≠ 0) ∨ (¬v.val a ≠ 0 ∧ w.val a ≠ 0), {
      intros a,
      dsimp [binary_module.add, premodel.act],
      dsimp [vect.unzip_fam, vect.map, vect.foldl],
      rw [ff_bxor_safe],
      calc
        bxor (v.val a) (w.val a) ≠ 0
            ↔ bxor (v.val a) (w.val a) = tt : neq_ff_iff _
        ... ↔ v.val a ≠ w.val a : bxor_eq_tt_iff _ _
        ... ↔ (v.val a = tt ∧ w.val a = 0) ∨ (v.val a = 0 ∧ w.val a = tt)
            : bool.neq_iff (v.val a) (w.val a)
        ... ↔ (v.val a ≠ 0 ∧ ¬w.val a ≠ 0) ∨ (¬v.val a ≠ 0 ∧ w.val a ≠ ff)
            : or_congr
              (and_congr (neq_ff_iff _) (@decidable.not_not_iff (w.val a=0) (bool.decidable_eq _ _))).symm
              (and_congr (@decidable.not_not_iff (v.val a=0) (bool.decidable_eq _ _)) (neq_ff_iff _)).symm
    },
    let suppvw := l.of_iff this,
    cases @is_finite.has_exhaustive_list {x // v.val x ≠ 0} v.property with suppv,
    cases @is_finite.has_exhaustive_list {x // w.val x ≠ 0} w.property with suppw,
    specialize hvy suppv,
    specialize hwz suppw,
    rw [accum_partition (λ x, w.val x ≠ 0)] at hvy,
    rw [accum_partition (λ x, v.val x ≠ 0)] at hwz,
    rw [←suppv.subrestrict_underlying (λ x, w.val x≠ 0)] at hvy,
    rw [←suppv.subrestrict_underlying (λ x, ¬w.val x≠ 0)] at hvy,
    rw [←suppw.subrestrict_underlying (λ x, v.val x≠ 0)] at hwz,
    rw [←suppw.subrestrict_underlying (λ x, ¬v.val x≠ 0)] at hwz,
    let suppv_only := suppv.subrestrict (λ x, ¬w.val x≠0),
    let suppv_w := suppv.subrestrict (λ x, w.val x≠0),
    unirewrite suppv.subrestrict (λ x, ¬w.val x≠0) with suppv_only at hvy,
    unirewrite suppv.subrestrict (λ x, w.val x≠0) with suppv_w at hvy,
    let suppw_only := suppw.subrestrict (λ x, ¬v.val x≠0),
    let suppw_v := suppw.subrestrict (λ x, v.val x≠0),
    unirewrite suppw.subrestrict (λ x, ¬v.val x≠0) with suppw_only at hwz,
    unirewrite suppw.subrestrict (λ x, v.val x≠0) with suppw_v at hwz,
    dsimp only [] at hvy hwz,
    let suppw_only' := suppw_only.of_iff (λ x, @and.comm (w.val x≠ 0) (¬v.val x≠ 0)),
    rw [←suppw_only.of_iff_underlying _] at hwz,
    unirewrite (suppw_only.of_iff _) with suppw_only' at hwz,
    have : list.perm suppv_w.underlying suppw_v.underlying, {
      rw [←suppw_v.of_iff_underlying (λ x, @and.comm (w.val x≠0) (v.val x≠0))],
      exact suppv_w.underlying_perm _
    },
    symmetry,
    calc
      y+z = (accum f suppv_w.underlying + accum f suppv_only.underlying)
            + (accum f suppw_v.underlying + accum f suppw_only'.underlying)
            : by rw [←hvy,←hwz]
      ... = (accum f suppv_w.underlying + accum f suppv_only.underlying)
            + (accum f suppv_w.underlying + accum f suppw_only'.underlying)
            : by rw [accum_perm this]
      ... = (accum f suppv_w.underlying + accum f suppv_only.underlying)
            + (-accum f suppv_w.underlying + accum f suppw_only'.underlying)
            : rfl
      ... = accum f suppv_only.underlying + accum f suppw_only'.underlying
            : by rw [add_comm (accum f suppv_w.underlying) _];
                 rw [add_assoc,←_root_.add_assoc (accum f suppv_w.underlying)];
                 rw [add_neg (accum f suppv_w.underlying)];
                 rw [zero_add]
      ... = accum f (suppv_only.union suppw_only').underlying
            : by rw [exhaustive_list.disjoint_union_underlying (λ x (h : (¬v.val x = 0 ∧ ¬¬w.val x = 0) ∧ ¬v.val x ≠ 0 ∧ w.val x ≠ 0), h.left.right h.right.right)];
                 rw [←accum_append]
      ... = accum f suppvw.underlying
            : accum_perm (suppvw.underlying_perm (suppv_only.union (suppw_only.of_iff (λ x, @and.comm (w.val x≠ 0) (¬v.val x≠ 0))))).symm
      ... = accum f l.underlying : congr_arg (accum f) (l.of_iff_underlying _)
  --/
  end

namespace unsafe

local attribute [instance] model.unsafe.pi

/- TO DO: prove `finite_bite α` is free with basis `α`. -/

end unsafe

end binary_module
