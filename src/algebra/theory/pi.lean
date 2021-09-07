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

--- The evaluation defines a morphism from the pi-type to its component.
definition pi_eval {th : theory} {α : Type _} (M : α → Type _) [∀ a, premodel th (M a)] (a : α) : morphism th (Π a, M a) (M a) :=
  ⟨(λ f, f a), by intros _ μ fs; rw [←vect.unzip_fam_eval]; unfold act⟩

end premodel

namespace model

--- The Pi-type of a family of models is virtually a model; i.e.~ up to `funext`.
theorem pi_axiom {th : theory} {α : Type _} {C : α → Type _} [∀ a, model th (C a)] : ∀ {n : ℕ} (r : th.rel n) (var : finord n → Π (a : α), C a) (a : α), optree.elim (@premodel.act th (Π a, C a) _) var (th.rel_lhs r) a = optree.elim (@premodel.act th (Π a, C a) _) var (th.rel_rhs r) a :=
  begin
    intros _ r var a,
    unfold premodel.act at *; dsimp *,
    let dact : Π (a : α) {k : ℕ}, th.op k → vect (C a) k → (C a) := λ a k f rs , premodel.act f rs,
    let dvar : Π (a : α), finord n → (C a) := λ k a, var a k,
    rw [@optree.elim_pi th.op _ α C dact dvar _ a],
    rw [@optree.elim_pi th.op _ α C dact dvar _ a],
    rw [axiom_eq]
  end

#print axioms pi_axiom

namespace unsafe
-- WARNING: Use of `funext`.

--- The Pi-type of a family of models is a model.
definition pi {th : theory} {α : Type _} {C : α → Type _} [∀ a, model th (C a)] : model th (Π a, C a):=
  {
    haxiom := λ _ r var, funext (pi_axiom r var)
  }

#print axioms model.unsafe.pi

end unsafe

end model
