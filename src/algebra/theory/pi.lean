import .basic

namespace premodel

--- The Pi-type of a family of premodels is a premodel, with the componentwise operations in terms of `vect.unzip_fam`.
definition pi {th : theory} {α : Type*} (M : α → Type _) [∀ a, premodel th (M a)] : premodel th (Π a, M a) :=
  {
    act :=
      λ n f xs, λ a,
        premodel.act f (xs.unzip_fam a)
  }

attribute [instance] premodel.pi

end premodel

namespace model

namespace unsafe
-- WARNING: Use of `funext`.

--- The Pi-type of a family of models is a model.
definition pi {th : theory} {α : Type _} {C : α → Type _} [∀ a, model th (C a)] : model th (Π a, C a):=
  {
    haxiom :=
      begin
        intros,
        apply funext,
        intro a,
        unfold premodel.act at *; dsimp *,
        let dact : Π (a : α) {k : ℕ}, th.op k → vect (C a) k → (C a) := λ a k f rs , premodel.act f rs,
        let dvar : Π (a : α), finord n → (C a) := λ k a, var a k,
        rw [@optree.elim_pi th.op _ α C dact dvar _ a],
        rw [@optree.elim_pi th.op _ α C dact dvar _ a],
        rw [axiom_eq]
      end
  }

#print axioms model.unsafe.pi

end unsafe

end model
