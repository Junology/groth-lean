/-
**
** The algebraic theory of F2-vector spaces.
**
-/

import data.bool.partial
import data.bool.misc

import algebra.theory
import algebra.free_model

import logic.misc

/-
 * Basic operations and relations
-/
namespace binary_module

inductive ops : ℕ → Type
| zero : ops 0
| add : ops 2

inductive rels : ℕ → Type
| left_zero : rels 1
| right_zero : rels 1
| add_self : rels 1
| add_comm : rels 2
| add_assoc : rels 3

end binary_module

--- The theory of F2-vector spaces
@[reducible]
definition binary_module : theory :=
{
  op := binary_module.ops,
  rel := binary_module.rels,
  rel_lhs :=
    @binary_module.rels.rec (λ n _, optree binary_module.ops (finord n))
      ⦃binary_module.ops.add | ⦃binary_module.ops.zero|⦄, ◎finord.fz⦄
      ⦃binary_module.ops.add | ◎finord.fz, ⦃binary_module.ops.zero|⦄⦄
      ⦃binary_module.ops.add | ◎finord.fz, ◎finord.fz⦄
      ⦃binary_module.ops.add | ◎finord.fz, ◎finord.fz.fs⦄
      ⦃binary_module.ops.add | ⦃binary_module.ops.add | ◎finord.fz, ◎finord.fz.fs⦄,◎finord.fz.fs.fs⦄,
  rel_rhs :=
    @binary_module.rels.rec (λ n _, optree binary_module.ops (finord n))
      (◎finord.fz)
      (◎finord.fz)
      ⦃binary_module.ops.zero|⦄
      ⦃binary_module.ops.add | ◎finord.fz.fs, ◎finord.fz⦄
      ⦃binary_module.ops.add | ◎finord.fz, ⦃binary_module.ops.add | ◎finord.fz.fs, ◎finord.fz.fs.fs⦄⦄
}


/-
 * Primitive operations and propositions on F2-vector spaces
-/
namespace binary_module

@[reducible]
protected
definition zero (α : Type _) [hpm : premodel binary_module α] : α :=
  @premodel.act binary_module α hpm _ binary_module.ops.zero vect.nil

@[reducible]
protected
definition add {α : Type _} [hm : premodel binary_module α] : α → α → α :=
  λ a b, @premodel.act binary_module α hm _ binary_module.ops.add (vect.cons a (vect.cons b vect.nil))

@[simp]
lemma zero_add {α : Type _} [model binary_module α] : ∀ a, binary_module.add (binary_module.zero α) a = a :=
  begin
    intro a,
    let h := model.axiom_eq binary_module α binary_module.rels.left_zero (λ _,a),
    dsimp [binary_module] at h,
    repeat { unfold optree.elim at h; try {unfold optree.elim_aux at h} },
    dunfold binary_module.add,
    dunfold binary_module.zero,
    assumption
  end

@[simp]
lemma add_zero {α : Type _} [model binary_module α] : ∀ a, binary_module.add a (binary_module.zero α) = a :=
  begin
    intro a,
    let h := model.axiom_eq binary_module α binary_module.rels.right_zero (λ _,a),
    dsimp [binary_module] at h,
    repeat { unfold optree.elim at h; try {unfold optree.elim_aux at h} },
    dunfold binary_module.add,
    dunfold binary_module.zero,
    assumption
  end

@[simp]
lemma add_self {α : Type _} [model binary_module α] : ∀ a, binary_module.add a a = binary_module.zero α :=
  begin
    intro a,
    let h := model.axiom_eq binary_module α binary_module.rels.add_self (λ_,a),
    dsimp [binary_module] at h,
    repeat { unfold optree.elim at h; try {unfold optree.elim_aux at h} },
    dunfold binary_module.add,
    dunfold binary_module.zero,
    assumption
  end

end binary_module


/-
 * F2-vector space structure on `bool`
-/

attribute [instance,reducible]
definition bool_bxor : model binary_module bool :=
{
  act := λ n f, vect.foldl bxor ff,--bool_bxor_act,
  haxiom :=
    begin
      intros,
      cases r,
      case binary_module.rels.left_zero {
        dsimp [binary_module],
        repeat { unfold optree.elim; try {unfold optree.elim_aux} },
        dunfold vect.foldl,
        exact ff_bxor _,
      },
      case binary_module.rels.right_zero {
        dsimp [binary_module],
        repeat { unfold optree.elim; try {unfold optree.elim_aux} },
        dunfold vect.foldl,
        rw [bxor_ff, ff_bxor]
      },
      case binary_module.rels.add_self {
        dsimp [binary_module],
        repeat { unfold optree.elim; try {unfold optree.elim_aux} },
        unfold vect.foldl,
        rw [ff_bxor],
        exact bxor_self _
      },
      case binary_module.rels.add_comm {
        dsimp [binary_module],
        repeat { unfold optree.elim; try {unfold optree.elim_aux} },
        unfold vect.foldl,
        rw [ff_bxor,ff_bxor],
        exact bxor_comm _ _
      },
      case binary_module.rels.add_assoc {
        dsimp [binary_module],
        repeat { unfold optree.elim; try {unfold optree.elim_aux} },
        unfold vect.foldl,
        repeat {rw [ff_bxor]},
        exact bxor_assoc _ _ _
      },
    end
}

namespace binary_module

definition generate {α : Type _} [model binary_module α] (a : α) : morphism binary_module bool α :=
{
  to_fun := @bool.rec (λ_, α) (binary_module.zero α) a,
  hact :=
    begin
      intros n f as,
      cases f,
      case binary_module.ops.zero {
        cases as,
        dsimp [premodel.act,vect.map,vect.foldl],
        unfold binary_module.zero,
      },
      case binary_module.ops.add {
        cases as with _ x bs; cases bs with _ y cs; cases cs,
        dsimp [premodel.act],
        cases x,
        case bool.ff {
          cases y,
          case bool.ff {
            let h := binary_module.add_zero (binary_module.zero α),
            unfold binary_module.add at h,
            have : (vect.foldl bxor ff (vect.cons ff (vect.cons ff vect.nil)))=ff,
              by refl,
            rw [this]; dsimp at *,
            unfold vect.map,
            rw [h],
          },
          case bool.tt {
            let h := binary_module.zero_add a,
            unfold binary_module.add at h,
            have : (vect.foldl bxor ff (vect.cons ff (vect.cons tt vect.nil)))=tt,
              by refl,
            rw [this]; dsimp at *,
            unfold vect.map,
            rw [h]
          }
        },
        case bool.tt {
          cases y,
          case bool.ff {
            let h := binary_module.add_zero a,
            unfold binary_module.add at h,
            have : (vect.foldl bxor ff (vect.cons tt (vect.cons ff vect.nil)))=tt,
              by refl,
            rw [this]; dsimp *,
            unfold vect.map,
            rw [h]
          },
          case bool.tt {
            let h := binary_module.add_self a,
            unfold binary_module.add at h,
            have : (vect.foldl bxor ff (vect.cons tt (vect.cons tt vect.nil)))=ff,
              by refl,
            rw [this]; dsimp *,
            unfold vect.map,
            rw [h]
          }
        },
      }
    end
}

#print axioms binary_module.generate

theorem bool_free : is_free binary_module (function.const unit tt) :=
  begin
    dunfold is_free,
    intros γ hmc f,
    existsi @generate _ hmc (f ()),
    split; dsimp *,
    focus {
      intro a; cases a,
      unfold generate
    },
    focus {
      intros g hy,
      cases g,
      unfold generate,
      simp * at *,
      unfold function.const at hy,
      apply funext,
      intros b,
      cases b,
      case bool.ff {
        let h := g_hact binary_module.ops.zero vect.nil,
        unfold premodel.act at h,
        unfold vect.foldl at h,
        dsimp * at *,
        rw [h],
        refl
      },
      case bool.tt {
        dsimp *,
        rw [hy]
      },
    }
  end

#print axioms binary_module.bool_free

end binary_module

@[instance]
definition bool_p_bxor (p : Prop) : model binary_module (bool_p p) :=
{
  act := λ n f, vect.foldl bxor_p (ff_p p),--bool_p_bxor_act p,
  haxiom :=
    begin
      intros n r var,
      cases r,
      case binary_module.rels.left_zero {
        dsimp [binary_module],
        repeat { unfold optree.elim; try {unfold optree.elim_aux} },
        dunfold vect.foldl,
        exact ff_bxor_p _
      },
      case binary_module.rels.right_zero {
        dsimp [binary_module],
        repeat { unfold optree.elim; try {unfold optree.elim_aux} },
        dunfold vect.foldl,
        rw [bxor_p_ff,ff_bxor_p],
      },
      case binary_module.rels.add_self {
        dsimp [binary_module],
        repeat { unfold optree.elim; try {unfold optree.elim_aux} },
        dunfold vect.foldl,
        rw [ff_bxor_p,bxor_p_self]
      },
      case binary_module.rels.add_comm {
        dsimp [binary_module],
        repeat { unfold optree.elim; try {unfold optree.elim_aux} },
        dunfold vect.foldl,
        csimp only [ff_bxor_p,bxor_p_comm]
      },
      case binary_module.rels.add_assoc {
        dsimp [binary_module],
        repeat { unfold optree.elim; try {unfold optree.elim_aux} },
        dunfold vect.foldl,
        csimp only [ff_bxor_p,bxor_p_assoc]
      },
    end
}

namespace binary_module

@[reducible]
definition generate_p (p : Prop) {α : Type _} [model binary_module α] (a : p → α) : morphism binary_module (bool_p p) α :=
{
  to_fun := λ x, @subtype.rec_on _ _ (λ_, α) x (λ b, @bool.cases_on (λ b, p∨b=ff → α) b (λ_, binary_module.zero α) (λ h, a (or.elim h id (λ h, by injection h)))),
  hact :=
    begin
      intros n f as,
      dsimp *,
      cases f,
      case binary_module.ops.zero {
        cases as,
        dsimp [premodel.act,vect.map,vect.foldl],
        unfold binary_module.zero,
      },
      case binary_module.ops.add {
        cases as with _ x bs; cases bs with _ y cs; cases cs,
        dsimp [premodel.act],
        cases x; cases x_val,
        case bool.ff {
          cases y; cases y_val,
          case bool.ff {
            let h := binary_module.add_zero (binary_module.zero α),
            unfold binary_module.add at h,
            have : vect.foldl bxor_p (ff_p p) (vect.cons ⟨ff, x_property⟩ (vect.cons ⟨ff, y_property⟩ vect.nil)) = ff_p p,
              by refl,
            rw [this],
            unfold vect.map,
            rw [h],
          },
          case bool.tt {
            have : p, from or.elim y_property id (λ h, by injection h),
            let h := binary_module.zero_add (a this),
            unfold binary_module.add at h,
            have : vect.foldl bxor_p (ff_p p) (vect.cons ⟨ff, x_property⟩ (vect.cons ⟨tt, y_property⟩ vect.nil)) = tt_p (y_property.elim id (λ x, by injection x)),
              by refl,
            rw [this],
            unfold vect.map,
            rw [h],
          }
        },
        case bool.tt {
          cases y; cases y_val,
          case bool.ff {
            have : p, from or.elim x_property id (λ h, by injection h),
            let h := binary_module.add_zero (a this),
            unfold binary_module.add at h,
            have : vect.foldl bxor_p (ff_p p) (vect.cons ⟨tt, x_property⟩ (vect.cons ⟨ff, y_property⟩ vect.nil)) = tt_p (x_property.elim id (λ x, by injection x)),
              by refl,
            rw [this],
            unfold vect.map,
            rw [h]
          },
          case bool.tt {
            have : p, from or.elim x_property id (λ h, by injection h),
            let h := binary_module.add_self (a this),
            unfold binary_module.add at h,
            have : vect.foldl bxor_p (ff_p p) (vect.cons ⟨tt, x_property⟩ (vect.cons ⟨tt, y_property⟩ vect.nil)) = ff_p p,
              by refl,
            rw [this],
            unfold vect.map,
            rw [h]
          }
        }
      }
    end
}

#print axioms generate_p

theorem bool_p_free (p : Prop) : is_free binary_module (@tt_p p) :=
  begin
    intros γ mc f,
    existsi @generate_p _ _ mc f,
    split; dsimp *,
    focus {
      intro; refl
    },
    focus {
      intros g hg,
      cases g,
      unfold generate_p,
      simp *,
      apply funext,
      intros x,
      cases x,
      cases x_val,
      case bool.ff {
        dsimp * at *,
        let h := g_hact binary_module.ops.zero vect.nil,
        dsimp [premodel.act,vect.foldl] at h,
        rw [h],
        refl
      },
      case bool.tt {
        dsimp * at *,
        have : p,
          from x_property.elim id (λ h, by injection h),
        exact hg this
      },
    }
  end

#print axioms bool_p_free

end binary_module
