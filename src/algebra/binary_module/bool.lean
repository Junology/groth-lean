import data.bool.partial
import data.bool.misc

import algebra.theory
import algebra.free_model
import algebra.binary_module.basic

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
