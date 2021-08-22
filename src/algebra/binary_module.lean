import algebra.theory
import algebra.free_model

import logic.misc

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

open optree

definition rel_lhs : ∀ n, rels n → optree ops (finord n)
| _ rels.left_zero := ⦃ops.add | ⦃ops.zero|⦄, ◎finord.fz⦄
| _ rels.right_zero := ⦃ops.add | ◎finord.fz, ⦃ops.zero|⦄⦄
| _ rels.add_self := ⦃ops.add | ◎finord.fz, ◎finord.fz⦄
| _ rels.add_comm := ⦃ops.add | ◎finord.fz, ◎finord.fz.fs⦄
| _ rels.add_assoc := ⦃ops.add | ⦃ops.add | ◎finord.fz, ◎finord.fz.fs⦄, ◎finord.fz.fs.fs⦄

definition rel_rhs : ∀ n, rels n → optree ops (finord n)
| _ rels.left_zero := ◎finord.fz
| _ rels.right_zero := ◎finord.fz
| _ rels.add_self := ⦃ops.zero|⦄
| _ rels.add_comm := ⦃ops.add | ◎finord.fz.fs, ◎finord.fz⦄
| _ rels.add_assoc := ⦃ops.add | ◎finord.fz, ⦃ops.add | ◎finord.fz.fs, ◎finord.fz.fs.fs⦄⦄

end binary_module

definition binary_module : theory :=
{
  op := binary_module.ops,
  rel := binary_module.rels,
  rel_lhs := binary_module.rel_lhs,
  rel_rhs := binary_module.rel_rhs
}

definition Ω_dec := {p // is_binary p}

instance omega_idecidable (p : Ω_dec) : idecidable p.val :=
  {is_either := p.property}

definition omega_xor_act : ∀ n, binary_module.op n → vect Ω_dec n → Ω_dec
| _ binary_module.ops.zero vect.nil := ⟨false, or.inr false.elim⟩
| _ binary_module.ops.add (vect.cons p (vect.cons q _)) :=
  ⟨xor p.val q.val, xor_binary p.property q.property⟩

#print axioms omega_xor_act

definition omega_xor : model binary_module {p // p ∨ ¬p} :=
{
  act := omega_xor_act,
  haxiom :=
    begin
      intros,
      cases r,
      case left_zero {
        dsimp [binary_module],
        dsimp [binary_module.rel_lhs,binary_module.rel_rhs],
        repeat { unfold optree.elim; try {unfold optree.elim_aux} },
        unfold omega_xor_act,
        apply subtype.eq; unfold subtype.val,
        exact propext (false_xor _),
      },
      case right_zero {
        dsimp [binary_module],
        dsimp [binary_module.rel_lhs,binary_module.rel_rhs],
        repeat { unfold optree.elim; try {unfold optree.elim_aux} },
        unfold omega_xor_act,
        apply subtype.eq; unfold subtype.val,
        exact propext (xor_false _)
      },
      case add_self {
        dsimp [binary_module,binary_module.rel_lhs,binary_module.rel_rhs],
        repeat { unfold optree.elim; try {unfold optree.elim_aux} },
        unfold omega_xor_act,
        apply subtype.eq; unfold subtype.val,
        exact propext (xor_self _)
      },
      case add_comm {
        dsimp [binary_module],
        delta binary_module.rel_lhs,
        delta binary_module.rel_rhs,
        dsimp *,
        delta id_rhs,
        repeat { unfold optree.elim; try {unfold optree.elim_aux} },
        unfold omega_xor_act,
        apply subtype.eq; unfold subtype.val,
        exact propext (xor_comm _ _)
      },
      case add_assoc {
        dsimp [binary_module],
        delta binary_module.rel_lhs,
        delta binary_module.rel_rhs,
        dsimp *,
        delta id_rhs,
        repeat { unfold optree.elim; try {unfold optree.elim_aux} },
        unfold omega_xor_act,
        apply subtype.eq; unfold subtype.val,
        exact propext (xor_assoc _ _ _)
      }
    end
}

#print axioms omega_xor
