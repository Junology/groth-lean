import .basic

namespace premodel

-- `optree` defines an (initial) premodel
instance tree_premodel (th : theory) (α : Type*) : premodel th (optree th.op α) :=
  {
    act := @optree.opnode th.op α
  }

end premodel


namespace morphism

-- maps into premodels give rise to morphisms out of trees
definition treelift (th : theory) {α β: Type*} [premodel th β] (f : α → β) : morphism th (optree th.op α) β :=
  subtype.mk (optree.elim (@premodel.act th β _) f) $
    by intros n μ ts; unfold premodel.act; rw [optree.elim_opnode]

-- Computation rule for treelift; treelift preserves the original map
theorem treelift_comp {th : theory} {α β: Type*} [premodel th β] (f : α → β) : ∀ {a : α}, (treelift th f).val (optree.varleaf a) = f a :=
  begin
    intros,
    dsimp [treelift],
    exact optree.elim_varleaf
  end

-- The embedding into a treemodel is "epimorphic"
mutual theorem tree_unique, tree_unique_aux {th : theory} {α β : Type*} [premodel th β] {f g : morphism th (optree th.op α) β} (h : ∀ a, f.val (optree.varleaf a) = g.val (optree.varleaf a))
with tree_unique : ∀ {t : optree th.op α}, f.val t = g.val t
| (optree.varleaf a) := h a
| (optree.opnode k vect.nil) :=
  begin
    have : (optree.opnode k vect.nil) = (@premodel.act th (optree th.op α) _ 0 k) vect.nil,
      by unfold premodel.act; refl,
    rw [this],
    rw [f.property,g.property],
    unfold vect.map
  end
| (optree.opnode k (vect.cons t ts)) :=
  begin
    have : ∀ t, (optree.opnode k t) = (@premodel.act th (optree th.op α) _ _ k) t,
      from λ_, rfl,
    rw [this],
    rw [f.property,g.property],
    unfold vect.map,
    rw [tree_unique, tree_unique_aux]
  end
with tree_unique_aux : ∀ {n : ℕ} {ts : vect (optree th.op α) n}, vect.map f.val ts = vect.map g.val ts
| _ vect.nil := by unfold vect.map; refl
| _ (vect.cons t ts) :=
  begin
    unfold vect.map,
    rw [tree_unique, tree_unique_aux],
    try {split; refl}
  end

end morphism
