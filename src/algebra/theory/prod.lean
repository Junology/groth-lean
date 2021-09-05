import .basic

/-!
 * Products of premodels are a premodel.
 * Operations are given in terms of `prod.map`.
-/
namespace premodel

--- A product of two premodels is a premodel; operations are given in terms of `prod.map`.
definition prod {th : theory} (α β : Type _) [premodel th α] [premodel th β] : premodel th (α×β):=
  {
    act :=
      λ (n : ℕ) (f : th.op n), prod.map (premodel.act f) (premodel.act f) ∘ vect.unzip
  }

attribute [instance] premodel.prod

end premodel


/-!
 * Products of models are a model.
 * Operations are given in terms of `prod.map`.
 * Axioms are verified componentwisely.
-/
namespace model

--- Product of two models is a model
definition prod {th : theory} (α β : Type _) [model th α] [model th β] : model th (α×β) :=
  {
    haxiom :=
      begin
        intros,
        unfold premodel.act,
        rw [optree.elim_prod,optree.elim_prod],
        rw [axiom_eq,axiom_eq]
      end
  }

#print axioms model.prod

end model


/-!
 * Structure morphisms on products are all morphisms.
 -/
namespace morphism

--- the projection onto the first component is a morphism of models
definition fst_is_morphism {th : theory} {α β : Type _} [premodel th α] [premodel th β] : is_morphism th (@prod.fst α β)
| _ μ vect.nil := rfl
| _ μ (vect.cons x xs) :=
  by dsimp [premodel.act,vect.unzip,prod.map,prod.fst,vect.map]; rw [vect.unzip_fst_is_map_fst]

#print axioms fst_is_morphism

--- the projection onto the second component is a morphism of models
definition snd_is_morphism {th : theory} {α β : Type _} [premodel th α] [premodel th β] : is_morphism th (@prod.snd α β)
| _ μ vect.nil := rfl
| _ μ (vect.cons x xs) :=
  by dsimp [premodel.act,vect.unzip,prod.map,prod.fst,vect.map]; rw [vect.unzip_snd_is_map_snd]

#print axioms snd_is_morphism

--- the morphism that projects the first component of products.
definition proj_fst (th : theory) {α β : Type*} [premodel th α] [premodel th β] : morphism th (α×β) α :=
{
  to_fun := @prod.fst α β,
  hact := @fst_is_morphism th α β _ _
}

--- the morphism that projects the second component of products.
definition proj_snd (th : theory) {α β : Type*} [premodel th α] [premodel th β] : morphism th (α×β) β :=
{
  to_fun := @prod.snd α β,
  hact := @snd_is_morphism th α β _ _
}

end morphism
