import algebra.optree
import data.vect.basic
import data.finite.finord

universes u v

-- Structure for algebraic theories
structure theory :=
  mk :: (op : ℕ → Type) (rel : ℕ → Type)
        (rel_lhs : ∀ {n : ℕ}, rel n → optree op (finord n))
        (rel_rhs : ∀ {n : ℕ}, rel n → optree op (finord n))


-- Pre-model of a theory; i.e. sets with structure maps which not necessarily satisfy the axioms.
class premodel (th : theory) (α : Type u) : Type u :=
  mk :: (act : Π {n : ℕ}, th.op n → vect α n → α)

-- Model of a theory
class model (th : theory) (α : Type u) extends premodel th α : Type u:=
  mk :: (haxiom : ∀ {n : ℕ} (r : th.rel n) (var : finord n → α), (th.rel_lhs r).elim @act var = (th.rel_rhs r).elim @act var)

instance model_is_premodel(th : theory) (α : Type _) [ha : model th α] : premodel th α := ha.to_premodel


namespace premodel

definition action (th : theory) (α : Type _) [premodel th α] : Π {n : ℕ}, th.op n → vect α n → α := @premodel.act th α _

-- Product of two premodels
definition prod {th : theory} (α β : Type _) [premodel th α] [premodel th β] : premodel th (α×β):=
  {
    act :=
      λ (n : ℕ) (f : th.op n), prod.map (premodel.act f) (premodel.act f) ∘ vect.unzip
  }

attribute [instance] premodel.prod

-- Product of families of premodels
definition pi {th : theory} {α : Type*} (M : α → Type _) [∀ a, premodel th (M a)] : premodel th (Π a, M a) :=
  {
    act :=
      λ n f xs, λ a,
        premodel.act f (xs.unzip_fam a)
  }

attribute [instance] premodel.pi

-- optree
instance tree_model (th : theory) (α : Type*) : premodel th (optree th.op α) :=
  {
    act := @optree.opnode th.op α
  }

end premodel

namespace model

definition axiom_eq (th : theory) (α : Type _) [model th α] : ∀ {n : ℕ} (r : th.rel n) (var : finord n → α), (th.rel_lhs r).elim (@premodel.act th α _) var = (th.rel_rhs r).elim (@premodel.act th α _) var := @model.haxiom th α _

-- Product of two models is a model
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

-- Product of families of models is a model
-- WARNING: This requires function extensionality
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

#print axioms model.pi

end model


/-*****************************
 - Morphisms of pre-models
 -*****************************-/

structure morphism (th : theory) (α : Type u) (β : Type v) [premodel th α] [premodel th β] : Type.{max u v+1}:=
  mk :: (to_fun : α → β) (hact : ∀ {n : ℕ} (f : th.op n) (as : vect α n), to_fun (@premodel.act th α _ _ f as) = (@premodel.act th β _ _ f (as.map to_fun)))

namespace morphism

protected
definition coe_to_fun {th : theory} (α : Type _) (β : Type _) [premodel th α] [premodel th β] : has_coe_to_fun (morphism th α β)  :=
  {
    F := λ_, α → β,
    coe := morphism.to_fun
  }

attribute [instance] morphism.coe_to_fun

-- the identity morphism
definition id {th : theory} {α : Type _} [premodel th α] : morphism th α α :=
  {
    to_fun := id,
    hact := by intros; rw [vect.map_id]; refl
  }

-- the composition of morphisms
definition comp {th : theory} {α β γ : Type _} [premodel th α] [premodel th β] [premodel th γ] : morphism th β γ → morphism th α β → morphism th α γ :=
  λ g f,
    {
      to_fun := g.to_fun ∘ f.to_fun,
      hact :=
        begin
          intros n k cs,
          unfold function.comp,
          rw [vect.map_comp],
          rw [f.hact,g.hact]
        end
    }

#print axioms morphism.comp

-- maps into premodels give rise to morphisms out of trees
definition treelift (th : theory) {α β: Type*} [premodel th β] (f : α → β) : morphism th (optree th.op α) β :=
  {
    to_fun := optree.elim (@premodel.act th β _) f,
    hact :=
      begin
        intros n k ts,
        unfold premodel.act,
        rw [optree.elim_opnode]
      end
  }

#print axioms treelift

-- treelift preserves the original map
theorem treelift_comp {th : theory} {α β: Type*} [premodel th β] (f : α → β) : ∀ {a : α}, (treelift th f).to_fun (optree.varleaf a) = f a :=
  begin
    intros,
    dsimp [treelift],
    exact optree.elim_varleaf
  end

#print axioms treelift_comp

-- The embedding into a treemodel is "epimorphic"
mutual theorem tree_unique, tree_unique_aux {th : theory} {α β : Type*} [premodel th β] {f g : morphism th (optree th.op α) β} (h : ∀ a, f.to_fun (optree.varleaf a) = g.to_fun (optree.varleaf a))
with tree_unique : ∀ {t : optree th.op α}, f.to_fun t = g.to_fun t
| (optree.varleaf a) := h a
| (optree.opnode k vect.nil) :=
  begin
    have : (optree.opnode k vect.nil) = (@premodel.act th (optree th.op α) _ 0 k) vect.nil,
      by unfold premodel.act; refl,
    rw [this],
    rw [f.hact,g.hact],
    unfold vect.map
  end
| (optree.opnode k (vect.cons t ts)) :=
  begin
    have : ∀ t, (optree.opnode k t) = (@premodel.act th (optree th.op α) _ _ k) t,
      from λ_, rfl,
    rw [this],
    rw [f.hact,g.hact],
    unfold vect.map,
    rw [tree_unique, tree_unique_aux]
  end
with tree_unique_aux : ∀ {n : ℕ} {ts : vect (optree th.op α) n}, vect.map f.to_fun ts = vect.map g.to_fun ts
| _ vect.nil := by unfold vect.map; refl
| _ (vect.cons t ts) :=
  begin
    unfold vect.map,
    rw [tree_unique, tree_unique_aux],
    try {split; refl}
  end

#print axioms tree_unique

-- Two morphisms equal to each other as soon as their underlying maps do
theorem morphism_eq {th : theory} {α β : Type _} [premodel th α] [premodel th β] {f g : morphism th α β} : f.to_fun = g.to_fun → f = g :=
  begin
    intros h,
    cases f,
    cases g,
    unfold morphism.to_fun at h,
    cases h,
    refl
  end

#print axioms morphism_eq

-- The image of every morphism is closed under operations
theorem image_act {th : theory} {α β : Type _} [premodel th α] [premodel th β] (f : morphism th α β) : ∀ {n : ℕ} {k : th.op n} {ys : vect {b // ∃ a, f.to_fun a = b} n}, ∃ a, f.to_fun a = (@premodel.act th β _ _ k) (vect.map subtype.val ys) :=
  begin
    intros,
    apply exists.elim (vect.image ys),
    intros as has,
    existsi (@premodel.act th α _ _ k) as,
    rw [f.hact, has]
  end

#print axioms image_act

-- The image of a morphism forms a premodel
definition image_premodel {th : theory} {α β : Type _} [premodel th α] [premodel th β] (f : morphism th α β) : premodel th {b // ∃ a, f.to_fun a = b} :=
  {
    act :=
      λ n k xs, ⟨@premodel.act th β _ _ k (vect.map subtype.val xs), image_act f⟩
  }

-- The image of a morphism in a model forms a model
definition image_model {th : theory} {α β : Type _} [premodel th α] [model th β] (f : morphism th α β) : model th {b // ∃ a, f.to_fun a = b} :=
  {
    to_premodel := image_premodel f,
    haxiom :=
      begin
        intros,
        dsimp [image_premodel] at *,
        apply subtype.eq,
        rw [optree.elim_subtype,optree.elim_subtype],
        rw [model.axiom_eq]
      end
  }

#print axioms image_model

end morphism
