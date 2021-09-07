import .basic

structure {u} inv_pred (th : theory) (α : Type u) [premodel th α] : Type (u+1) :=
  (p : α → Prop) (hinv : ∀ {n} (μ : th.op n) (as : vect α n), vect.is_all p as → p (premodel.act μ as))

definition submodel (th : theory) {α : Type _} [premodel th α] (p : inv_pred th α) := subtype p.p

namespace submodel

instance submodel_is_premodel (th : theory) {α : Type _} [premodel th α] (p : inv_pred th α) : premodel th (submodel th p) :=
{
  act := λ _ μ xs, ⟨premodel.act μ (xs.map subtype.val), p.hinv μ _ vect.is_all_subtype⟩
}

definition sub_incl (th : theory) {α : Type _} [premodel th α] (p : inv_pred th α) : morphism th (submodel th p) α :=
  ⟨subtype.val, λ _ _ _, rfl⟩

instance submodel_is_model (th : theory) {α : Type _} [model th α] (p : inv_pred th α) : model th (submodel th p) :=
{
  haxiom :=
    begin
      intros _ r var,
      apply subtype.eq,
      repeat { rw [@optree.elim_funap th.op _ (subtype p.p) α (@premodel.act th (submodel th p) _) (@premodel.act th α _) var subtype.val (sub_incl th p).property] },
      exact model.axiom_eq th α r _
    end
}

#print axioms submodel.submodel_is_model

end submodel
