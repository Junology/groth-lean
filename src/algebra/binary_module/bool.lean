import data.bool.subbool
import data.bool.misc

import algebra.theory
import algebra.theory.free
import .basic

/-
 * F2-vector space structure on `bool`
-/
attribute [instance,reducible]
definition bool_bxor : model binary_module bool :=
{
  act := λ n f, vect.foldl bxor ff,
  haxiom :=
    begin
      intros,
      cases r,
      case binary_module.rels.left_zero {
        dsimp [binary_module],
        repeat {
          csimp only [optree.elim_opnode,optree.elim_varleaf],
          try {dsimp [vect.map,vect.foldl]}
        },
        rw [ff_bxor_safe],
      },
      case binary_module.rels.right_zero {
        dsimp [binary_module],
        repeat {
          csimp only [optree.elim_opnode,optree.elim_varleaf],
          try {dsimp [vect.map,vect.foldl]}
        },
        rw [bxor_ff_safe, ff_bxor_safe]
      },
      case binary_module.rels.add_self {
        dsimp [binary_module],
        repeat {
          csimp only [optree.elim_opnode,optree.elim_varleaf],
          try {dsimp [vect.map,vect.foldl]}
        },
        rw [ff_bxor_safe],
        exact bxor_self_safe _
      },
      case binary_module.rels.add_comm {
        dsimp [binary_module],
        repeat {
          csimp only [optree.elim_opnode,optree.elim_varleaf],
          try {dsimp [vect.map,vect.foldl]}
        },
        rw [ff_bxor_safe,ff_bxor_safe],
        exact bxor_comm _ _
      },
      case binary_module.rels.add_assoc {
        dsimp [binary_module],
        repeat {
          csimp only [optree.elim_opnode,optree.elim_varleaf],
          try {dsimp [vect.map,vect.foldl]}
        },
        repeat {rw [ff_bxor_safe]},
        exact bxor_assoc _ _ _
      },
    end
}

#print axioms bool_bxor

namespace binary_module

definition generate {α : Type _} [model binary_module α] (a : α) : morphism binary_module bool α :=
{
  val := @bool.rec (λ_, α) (binary_module.zero α) a,
  property :=
    begin
      intros n f as,
      cases f,
      case binary_module.ops.zero {
        cases as,
        dsimp [premodel.act,vect.map,vect.foldl],
        dunfold binary_module.zero,
        refl
      },
      case binary_module.ops.add {
        cases as with _ x bs; cases bs with _ y cs; cases cs,
        dsimp [premodel.act],
        cases x,
        case bool.ff {
          cases y,
          case bool.ff {
            let h := binary_module.add_zero (binary_module.zero α),
            dunfold binary_module.add at h,
            have : (vect.foldl bxor ff (vect.cons ff (vect.cons ff vect.nil)))=ff,
              by refl,
            rw [this]; dsimp at *,
            dunfold vect.map,
            rw [h],
          },
          case bool.tt {
            let h := binary_module.zero_add a,
            dunfold binary_module.add at h,
            have : (vect.foldl bxor ff (vect.cons ff (vect.cons tt vect.nil)))=tt,
              by refl,
            rw [this]; dsimp at *,
            dunfold vect.map,
            rw [h]
          }
        },
        case bool.tt {
          cases y,
          case bool.ff {
            let h := binary_module.add_zero a,
            dunfold binary_module.add at h,
            have : (vect.foldl bxor ff (vect.cons tt (vect.cons ff vect.nil)))=tt,
              by refl,
            rw [this]; dsimp *,
            dunfold vect.map,
            rw [h]
          },
          case bool.tt {
            let h := binary_module.add_self a,
            dunfold binary_module.add at h,
            have : (vect.foldl bxor ff (vect.cons tt (vect.cons tt vect.nil)))=ff,
              by refl,
            rw [this]; dsimp *,
            dunfold vect.map,
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
      dunfold generate,
      dunfold function.const at hy,
      apply subtype.eq; dunfold subtype.val,
      apply funext,
      intros b,
      cases b,
      case bool.ff {
        let h := g.property binary_module.ops.zero vect.nil,
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
definition subbool_binmod (p : Prop) : model binary_module (subbool p) :=
{
  act := λ n f, vect.foldl subbool.xor (subbool.ff p),
  haxiom :=
    begin
      intros n r var,
      cases r,
      case binary_module.rels.left_zero {
        dsimp [binary_module],
        repeat { unfold optree.elim; try {unfold optree.elim_aux} },
        dunfold vect.foldl,
        exact subbool.ff_xor _
      },
      case binary_module.rels.right_zero {
        dsimp [binary_module],
        repeat { unfold optree.elim; try {unfold optree.elim_aux} },
        dunfold vect.foldl,
        rw [subbool.xor_ff,subbool.ff_xor],
      },
      case binary_module.rels.add_self {
        dsimp [binary_module],
        repeat { unfold optree.elim; try {unfold optree.elim_aux} },
        dunfold vect.foldl,
        rw [subbool.ff_xor, subbool.xor_self]
      },
      case binary_module.rels.add_comm {
        dsimp [binary_module],
        repeat { unfold optree.elim; try {unfold optree.elim_aux} },
        dunfold vect.foldl,
        csimp only [subbool.ff_xor, subbool.xor_comm]
      },
      case binary_module.rels.add_assoc {
        dsimp [binary_module],
        repeat { unfold optree.elim; try {unfold optree.elim_aux} },
        dunfold vect.foldl,
        csimp only [subbool.ff_xor, subbool.xor_assoc]
      },
    end
}

#print axioms subbool_binmod

namespace binary_module

@[reducible]
definition generate_p (p : Prop) {α : Type _} [model binary_module α] (a : p → α) : morphism binary_module (subbool p) α :=
{
  val := λ x, @subtype.rec_on _ _ (λ_, α) x (λ b, @bool.cases_on (λ b, p∨b=ff → α) b (λ_, binary_module.zero α) (λ h, a (or.elim h id (λ h, by injection h)))),
  property :=
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
            have : vect.foldl subbool.xor (subbool.ff p) ⁅⟨ff, x_property⟩, ⟨ff, y_property⟩⁆ = subbool.ff p,
              by refl,
            rw [this],
            unfold vect.map,
            rw [h],
          },
          case bool.tt {
            have : p, from or.elim y_property id (λ h, by injection h),
            let h := binary_module.zero_add (a this),
            unfold binary_module.add at h,
            have : vect.foldl subbool.xor (subbool.ff p) ⁅⟨ff, x_property⟩, ⟨tt, y_property⟩⁆ = subbool.tt (y_property.elim id (λ x, by injection x)),
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
            have : vect.foldl subbool.xor (subbool.ff p) ⁅⟨tt, x_property⟩, ⟨ff, y_property⟩⁆ = subbool.tt (x_property.elim id (λ x, by injection x)),
              by refl,
            rw [this],
            unfold vect.map,
            rw [h]
          },
          case bool.tt {
            have : p, from or.elim x_property id (λ h, by injection h),
            let h := binary_module.add_self (a this),
            unfold binary_module.add at h,
            have : vect.foldl subbool.xor (subbool.ff p) ⁅⟨tt, x_property⟩, ⟨tt, y_property⟩⁆ = subbool.ff p,
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

theorem subbool_free (p : Prop) : is_free binary_module (@subbool.tt p) :=
  begin
    intros γ mc f,
    existsi @generate_p _ _ mc f,
    split; dsimp *,
    focus {
      intro; refl
    },
    focus {
      intros g hg,
      unfold generate_p,
      simp *,
      apply subtype.eq; dunfold subtype.val,
      apply funext,
      intros x,
      cases x,
      cases x_val,
      case bool.ff {
        dsimp * at *,
        let h := g.property binary_module.ops.zero vect.nil,
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

#print axioms subbool_free

end binary_module
