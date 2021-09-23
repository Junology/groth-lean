import data.bool.misc
import data.list.misc
import logic.misc
import logic.finite
import tactic.unirewrite
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

--- `singlebit a` classifies `a`.
lemma singlebit_nonzero_iff {α : Type _} [decidable_eq α] {a : α} : ∀ x, (singlebit a).val x ≠ 0 ↔ x = a :=
  λ x, iff.intro
    (λ h,
      begin
        dsimp [singlebit] at h,
        by_cases hax: a=x,
        exact hax.symm,
        rw [to_bool_ff hax] at h,
        injection ((neq_ff_iff ff).mp h),
      end
    )
    (λ hxa h,
      begin
        dsimp [singlebit] at h;
        rw [to_bool_tt hxa.symm] at h;
        injection h
      end
    )

--- Support of `singlebit a` consists of only `a`.
lemma singlebit_support {α : Type _} [decidable_eq α] {a : α} : ∀ (l : exhaustive_list {x // (singlebit a).val x ≠ 0}), l.underlying = [a] :=
  begin
    intros l,
    calc
      l.underlying
          = (l.of_iff singlebit_nonzero_iff).underlying
            : (l.of_iff_underlying _).symm
      ... = (exhaustive_list.singleton a).underlying
            : by rw [(l.of_iff singlebit_nonzero_iff).singleton_unique]
      ... = [a] : rfl
  end

--- If `a` lies in the support of `w : finsupp_bits α`, then the support of `w + singlebit a` is exactly the support of `w` minus `a`.
lemma support_of_add_singlebit_of_nonzero {α : Type _} [decidable_eq α] {w : finsupp_bits α} {a : α} : w.val a ≠ 0 → ∀ (l : exhaustive_list {x // w.val x ≠ 0}) (la : exhaustive_list {x // w.val x + (singlebit a).val x ≠ 0}), list.perm l.underlying (a :: la.underlying) :=
  begin
    intros hwa l la,
    dsimp [singlebit] at la,
    have ha : a ∉ la.underlying, {
      intros h,
      let h' := (la.underlying_mem_iff a).mpr h,
      rw [(neq_ff_iff _).mp hwa, to_bool_tt rfl] at h',
      exact h' rfl
    },
    apply list.nodup_perm_of_mem
      l.underlying_nodup
      (list.nodup.cons ha la.underlying_nodup),
    intros x,
    split,
    show x ∈ l.underlying → _, {
      intros hx,
      by_cases hxa: a = x; try { exact or.inl hxa.symm },
      right,
      apply (la.underlying_mem_iff x).mp,
      apply (neq_ff_iff _).mpr,
      have : w.val x = tt,
        from (neq_ff_iff _).mp ((l.underlying_mem_iff x).mpr hx),
      rw [this, to_bool_ff hxa],
      refl
    },
    show x ∈ a :: la.underlying → _, {
      refine implies.trans _ (l.underlying_mem_iff x).mp,
      intros hx; cases hx,
      case or.inl { rw [hx]; exact hwa },
      case or.inr {
        have hax: a ≠ x,
          from (λ h, ha (by rw [←h] at hx; exact hx)),
        let hwxa := (la.underlying_mem_iff x).mpr hx,
        rw [to_bool_ff hax] at hwxa,
        intros h,
        rw [h] at hwxa,
        exact hwxa rfl
      }
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

--- `waccum` is just an evaluation on `singlebit`.
lemma waccum_funrel_single {α : Type _} [decidable_eq α] {φ : Type _} [model binary_module φ] (f : α → φ) : ∀ (a : α), (waccum_funrel f).p (singlebit a) (f a) :=
  begin
    intros a,
    dsimp [waccum_funrel],
    intros l,
    rw [singlebit_support],
    dsimp [accum],
    rw [add_zero]
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

open funrel.unsafe

local attribute [instance] model.unsafe.pi

variables {α : Type _} [decidable_eq α]

--- `finsupp_bits` is non-zero precisely if it has at least one `tt` bit.
lemma finsupp_bits.nonzero (w : finsupp_bits α) : w ≠ 0 → ∃ a, w.val a = tt :=
  begin
    intros hw,
    cases @is_finite.has_exhaustive_list _ w.property with l,
    cases hl: l.underlying with a tl,
    case nil {
      suffices : w = 0,
        by exfalso; exact hw this,
      unirewrite @has_zero.zero (finsupp_bits α) _ with binary_module.zero _,
      dsimp [binary_module.zero],
      apply subtype.eq,
      funext,
      dsimp [premodel.act],
      dsimp [vect.map, vect.unzip_fam, vect.foldl],
      cases (bool.decidable_eq (w.val x) ff),
      case is_false {
        exfalso,
        have : x ∈ l.underlying,
          from (l.underlying_mem_iff x).mp h,
        rw [hl] at this,
        exact list.not_mem_nil _ this
      },
      case is_true { exact h }
    },
    case cons {
      existsi a,
      apply (neq_ff_iff (w.val a)).mp,
      have : a ∈ l.underlying,
        by let h := list.mem_cons_self a tl; rw [←hl] at h; exact h,
      exact (l.underlying_mem_iff a).mpr this
    }
  end

-- Realization of the weighted accumuration `waccum_funrel` using `definite_description`.
noncomputable definition waccum {φ : Type _} [model binary_module φ] (f : α → φ) : finsupp_bits α → φ :=
  reify (waccum_funrel f)

noncomputable definition waccum_hom {φ : Type _} [model binary_module φ] (f : α → φ) : hom (finsupp_bits α) φ :=
  subtype.mk (waccum f) $
    begin
      intros _ μ as,
      dunfold waccum,
      cases μ,
      case ops.zero {
        cases as,
        dunfold vect.map,
        drefold binary_module.zero _,
        rw [iff.mp (reify_eq (waccum_funrel f)) (waccum_funrel_zero f)],
        refl
      },
      case ops.add {
        cases as with _ v vs; cases vs with _ w ws; cases ws,
        dunfold vect.map,
        drefold binary_module.add _ _,
        drefold binary_module.add _ _,
        unirewrite binary_module.add v w with has_add.add v w,
        let y := funrel.unsafe.reify (waccum_funrel f) v,
        let z := funrel.unsafe.reify (waccum_funrel f) w,
        unirewrite funrel.unsafe.reify (waccum_funrel f) v with y,
        unirewrite funrel.unsafe.reify (waccum_funrel f) w with z,
        have hvy : (waccum_funrel f).p v y,
          from iff.mpr (reify_eq (waccum_funrel f)) rfl,
        have hwz : (waccum_funrel f).p w z,
          from iff.mpr (reify_eq (waccum_funrel f)) rfl,
        apply iff.mp (reify_eq (waccum_funrel f)),
        apply waccum_funrel_add f v w y z hvy hwz
      }
    end

--- `waccum` is just the evaluation at `singlebit a`.
lemma waccum_single {φ : Type _} [model binary_module φ] (f : α → φ) : ∀ (a : α), waccum f (singlebit a) = f a :=
  begin
    intros a,
    apply iff.mp (reify_eq (waccum_funrel f)),
    exact waccum_funrel_single f a
  end

---`finsupp_bits α` is free with basis `α` provided `decidable_eq α`.
theorem finsupp_bits_free {φ : Type _} [model binary_module φ] (f : α → φ) : ∃! (g : morphism binary_module (finsupp_bits α) φ), ∀ a, g.val (singlebit a) = f a :=
  begin
    existsi waccum_hom f,
    dsimp [waccum_hom],
    split,
    show ∀ (a : α), _ = f a,
      from waccum_single f,
    show ∀ (g : morphism binary_module (finsupp_bits α) _), _, {
      intros g hg,
      apply subtype.eq; dsimp *,
      apply funext,
      suffices : ∀ (n : ℕ) (w : finsupp_bits α) (l : exhaustive_list {x // w.val x ≠ 0}), l.underlying.length = n → g.val w = waccum f w, {
        intros w,
        cases @is_finite.has_exhaustive_list _ w.property with l,
        exact this l.underlying.length w l rfl,
      },
      intros n,
      induction n with k h_ind,
      case zero {
        intros w l hl,
        suffices : w = binary_module.zero _, {
          repeat { rw [this] },
          unirewrite waccum f with (waccum_hom f).val,
          rw [g.property ops.zero, (waccum_hom f).property ops.zero],
          dsimp [vect.map],
          refl
        },
        apply subtype.eq,
        funext,
        dsimp [binary_module.zero, premodel.act],
        dsimp [vect.map, vect.unzip_fam, vect.foldl],
        cases bool.decidable_eq (w.val x) ff,
        case is_true { exact h },
        exfalso,
        have hx : x ∈ l.underlying,
          from (l.underlying_mem_iff x).mp h,
        have : l.underlying = [],
          from list.eq_nil_of_length_eq_zero hl,
        rw [this] at hx,
        exact list.not_mem_nil x hx
      },
      case succ {
        intros w l hl_len,
        cases hl: l.underlying with a tl,
        case nil {
          exfalso,
          rw [hl] at hl_len,
          exact nat.succ_ne_zero _ hl_len.symm
        },
        have ha : w.val a ≠ 0, {
          apply (l.underlying_mem_iff a).mpr,
          rw [hl]; exact list.mem_cons_self _ _
        },
        have hwa : g.val (w + singlebit a) = waccum f (w + singlebit a), {
          cases @is_finite.has_exhaustive_list _ (w + singlebit a).property with la,
          apply h_ind _ la,
          apply nat.succ.inj,
          refine eq.trans _ hl_len,
          unirewrite nat.succ _ with _+1,
          drefold list.length (a::la.underlying),
          apply list.perm.length,
          symmetry,
          exact support_of_add_singlebit_of_nonzero ha l la,
        },
        calc
          g.val w
              = g.val (w + (singlebit a - singlebit a))
                : by rw [sub_self, add_zero]
          ... = g.val (w + (singlebit a + singlebit a))
                : by refl
          ... = g.val (w + singlebit a) + g.val (singlebit a)
                : by rw [←add_assoc, morphism.respect_add g]
          ... = waccum f (w + singlebit a) + f a
                : by rw [hwa,hg]
          ... = waccum f (w + singlebit a) + waccum f (singlebit a)
                : by rw [waccum_single f a]
          ... = waccum f (w + singlebit a + singlebit a)
                : by unirewrite waccum f with (waccum_hom f).val;
                     rw [←morphism.respect_add (waccum_hom f)]
          ... = waccum f (w + (singlebit a + singlebit a))
                : by rw [add_assoc]
          ... = waccum f w
                : by unirewrite @has_add.add (finsupp_bits α) _ (singlebit a) (singlebit a) with @has_sub.sub (finsupp_bits α) _ (singlebit a) (singlebit a);
                     rw [sub_self, add_zero]
      }
    --/
    }
  end

---`finsupp_bits α` is free with basis `α` provided `decidable_eq α`.
theorem finsupp_bits.is_free : is_free binary_module (@singlebit α _) :=
  @finsupp_bits_free α _

end unsafe

end binary_module
