import algebra.theory
import algebra.abelian

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

@[reducible,inline]
protected
definition zero (α : Type _) [hpm : premodel binary_module α] : α :=
  @premodel.act binary_module α hpm _ binary_module.ops.zero vect.nil

@[reducible,inline]
protected
definition add {α : Type _} [hm : premodel binary_module α] : α → α → α :=
  λ a b, @premodel.act binary_module α hm _ binary_module.ops.add (vect.cons a (vect.cons b vect.nil))

definition has_binary_zero (α : Type _) [premodel binary_module α] : has_zero α := has_zero.mk (binary_module.zero α)

--- Useful to define an instance of `has_add α` by `attribute [instance] has_binary_add α` if `α` is a premodel of binary_module.
definition has_binary_add (α : Type _) [premodel binary_module α] : has_add α := has_add.mk binary_module.add

definition has_binary_neg (α : Type _) [premodel binary_module α] : has_neg α := has_neg.mk id

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

@[simp]
lemma add_comm {α : Type _} [model binary_module α] : ∀ (a b : α), binary_module.add a b = binary_module.add b a :=
  begin
    intros a b,
    let h := model.axiom_eq binary_module α binary_module.rels.add_comm (λ (o : finord 2), @finord.cases_on (λ_ _,α) _ o (λ_, a) (λ _ _, b)),
    dsimp [binary_module] at h,
    repeat { unfold optree.elim at h; try {unfold optree.elim_aux at h} },
    dunfold binary_module.add,
    assumption
  end

@[simp]
lemma add_assoc {α : Type _} [model binary_module α] : ∀ (a b c : α), binary_module.add (binary_module.add a b) c = binary_module.add a (binary_module.add b c) :=
  begin
    intros a b c,
    let h := model.axiom_eq binary_module α binary_module.rels.add_assoc (λ (o : finord 3), @finord.cases_on (λ_ _,α) _ o (λ_, a) (λ _ o', @finord.cases_on (λ _ _,α) _ o' (λ _, b) (λ _ _, c))),
    dsimp [binary_module] at h,
    repeat { unfold optree.elim at h; try {unfold optree.elim_aux at h} },
    dunfold binary_module.add,
    assumption
  end

#print axioms binary_module.add_assoc

definition binary_abelian (α : Type _) [model binary_module α] : has_add_abelian α :=
{
  to_has_add := has_binary_add α,
  to_has_zero := has_binary_zero α,
  to_has_neg := has_binary_neg α,
  add_zero := binary_module.add_zero,
  add_neg := binary_module.add_self,
  add_comm := binary_module.add_comm,
  add_assoc := binary_module.add_assoc,
}

#print axioms binary_abelian

--- The constant map at `zero` yields a morphism of binary modules.
definition zero_morphism (α β : Type _) [model binary_module α] [model binary_module β] : morphism binary_module α β :=
{
  val := λ _, binary_module.zero β,
  property :=
    begin
      intros n μ as,
      rw [vect.map_const],
      dsimp *,
      cases μ,
      case binary_module.ops.zero {
        dsimp [vect.repeat],
        refl
      },
      case binary_module.ops.add {
        dunfold vect.repeat,
        have : ∀ (b : β), vect.repeat b ((1 : ℕ).add 0) = vect.cons b vect.nil := λ _,rfl,
        rw [this],
        let hz := @zero_add β _,
        dunfold binary_module.add at hz,
        rw [hz],
      }
    end
}

--- The trivial binary_module is an initial model.
definition unit_is_initial : model.is_initial binary_module unit :=
{
  elim := λ β hb, @zero_morphism unit β _ hb,
  hunique :=
    begin
      intros β mb g a,
      cases a,
      dsimp [zero_morphism],
      have : punit.star = @premodel.act binary_module unit _ 0 binary_module.ops.zero vect.nil := rfl,
      rw [this,g.property],
      refl
    end
}

#print axioms unit_is_initial


--- The theory `binary_module` has a trivial initial model.
instance has_trivial_init : model.has_trivial_init binary_module :=
{
  init_unit := binary_module.unit_is_initial
}

--- The fixed element is always the zero.
theorem fixed_elem_is_zero (α : Type _) [ha : model binary_module α] : @model.fixed_element binary_module binary_module.has_trivial_init α _ = @premodel.act binary_module α _ _ binary_module.ops.zero vect.nil :=
  model.fixed_const binary_module α binary_module.ops.zero

#print axioms fixed_elem_is_zero

end binary_module

