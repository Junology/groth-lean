
import logic.misc

attribute [reducible]
definition is_binary (p : Prop) : Prop := p ∨ ¬p

--- An "internal" version of decidability.
class idecidable (p : Prop) : Prop :=
  (is_either : is_binary p)

@[reducible]
definition idecidable_pred {α : Sort _} (p : α → Prop) :=
  ∀ a, idecidable (p a)

--- Class of types that has internally decidable equality.
@[reducible]
definition idecidable_eq (α : Sort _) : Prop := ∀ (a b : α), idecidable (a=b)

@[reducible]
def idecidable_rel {α : Sort _} (r : α → α → Prop) :=
  ∀ a b, idecidable (r a b)

@[elab_as_eliminator]
lemma whether (p : Prop) [idec : idecidable p] : p ∨ ¬ p :=
  idec.is_either

lemma not_binary {p : Prop} (hbp : is_binary p) : is_binary (¬p) :=
  begin
    apply or.elim hbp,
    show p → is_binary (¬p), { intro hp; right; exact not_not_intro hp},
    show ¬p → is_binary (¬p), { intro hnp; left; assumption },
  end

lemma or_binary {p q : Prop} (hbp : is_binary p) (hbq : is_binary q)  : is_binary (p∨ q) :=
  begin
    apply or.elim hbq; apply or.elim hbp,
    show p → q → is_binary (p∨ q), {
      intros hp hq,
      left; left; exact hp
    },
    show ¬p → q → is_binary (p∨ q), {
      intros hnp hq,
      left; right; exact hq
    },
    show p → ¬q → is_binary (p∨ q), {
      intros hp hnq,
      left; left; exact hp
    },
    show ¬p → ¬q → is_binary (p∨ q), {
      intros hnp hnq,
      right, intros hnpq,
      apply or.elim hnpq; intros; contradiction
    }
  end

lemma and_binary {p q : Prop} (hbp : is_binary p) (hbq : is_binary q) : is_binary (p∧q) :=
  begin
    apply or.elim hbq; apply or.elim hbp,
    show p → q → is_binary (p∧q), {
      intros hp hq,
      left; exact ⟨hp,hq⟩
    },
    show ¬p → q → is_binary (p∧q), {
      intros hnp hq,
      right; intros hnpq,
      exact hnp hnpq.left
    },
    show p → ¬q → is_binary (p∧q), {
      intros hp hnq,
      right; intros hnpq,
      exact hnq hnpq.right
    },
    show ¬p → ¬q → is_binary (p∧q), {
      intros hnp hnq,
      right; intros hnpq,
      exact hnp hnpq.left
    },
  end

lemma xor_binary {p q : Prop} (hbp : is_binary p) (hbq : is_binary q) : is_binary (xor p q) :=
  begin
    have hbnp : is_binary ¬p, from not_binary hbp,
    have hbnq : is_binary ¬q, from not_binary hbq,
    apply or_binary; apply and_binary; assumption
  end

instance not_idecidable (p : Prop) [idecidable p] : idecidable ¬p :=
  {is_either := not_binary (whether p)}
instance or_idecidable (p q : Prop) [idecidable p] [idecidable q] : idecidable (p∨q) :=
  {is_either := or_binary (whether p) (whether q)}
instance and_idecidable (p q : Prop) [idecidable p] [idecidable q] : idecidable (p∧q) :=
  {is_either := and_binary (whether p) (whether q)}
instance xor_idecidable (p q : Prop) [idecidable p] [idecidable q] : idecidable (xor p q) :=
  {is_either := xor_binary (whether p) (whether q)}

#print axioms xor_idecidable

lemma not_xor_iff {p q : Prop} [idecidable p] [idecidable q] : ¬xor p q → (p ↔ q) :=
  begin
    intros hnx,
    let h := not_or_distrib.mp hnx,
    apply or.elim (whether q); apply or.elim (whether p),
    show p → q → (p↔ q),
      from λ hp hq, {mp := (λ _, hq), mpr := (λ _, hp)},
    show ¬p → q → (p↔ q),
      from λ hnp hq, (h.right ⟨hq,hnp⟩).elim,
    show p → ¬q → (p↔ q),
      from λ hp hnq, (h.left ⟨hp,hnq⟩).elim,
    show ¬p → ¬q → (p↔ q),
      from λ hnp hnq, {mp := (λ hp, (hnp hp).elim), mpr := (λ hq, (hnq hq).elim)}
  end

private
lemma xor_assoc_impl (p q r : Prop) [idecidable p] [idecidable q] [idecidable r] : xor (xor p q) r → xor p (xor q r) :=
  begin
    intros h,
    apply or.elim h,
    show (xor p q) ∧ ¬r → xor p (xor q r), {
      intros hpqr,
      apply or.elim (whether r),
      show r → xor p (xor q r), {intro hr; exfalso; exact hpqr.right hr},
      intros hnr,
      apply or.elim hpqr.left,
      show p∧¬q → xor p (xor q r), {
        intros hpq,
        left; split; try {exact hpq.left},
        intros hx; apply or.elim hx,
        show q∧¬r → false, {
          intros hqr,
          exact hpq.right hqr.left
        },
        show r∧¬q → false, {
          intros hrq,
          exact hnr hrq.left
        },
      },
      show q∧¬p → xor p (xor q r), {
        intros hqr,
        right; split; try {exact hqr.right},
        exact or.inl ⟨hqr.left,hnr⟩
      }
    },
    show r ∧ ¬xor p q → xor p (xor q r), {
      intros hrpq,
      have hpq : p↔q, from not_xor_iff hrpq.right,
      apply or.elim (whether p),
      show p → xor p (xor q r), {
        intros hp,
        left; split; try {assumption},
        intros hx,
        apply or.elim hx,
        show q ∧ ¬r → false, {
          intro hqr,
          exact hqr.right hrpq.left
        },
        show r ∧ ¬q → false, {
          intro hrq,
          exact hrq.right (hpq.mp hp)
        },
      },
      show ¬p → xor p (xor q r), {
        intros hnp,
        right; split; try {assumption},
        right,
        exact ⟨hrpq.left, (λ hq, hnp (hpq.mpr hq))⟩
      }
    },
  end

definition xor_assoc (p q r : Prop) [idecidable p] [idecidable q] [idecidable r] : xor (xor p q) r ↔ xor p (xor q r) :=
{
  mp := xor_assoc_impl p q r,
  mpr :=
    by calc
      xor p (xor q r)
          → xor p (xor r q) : (xor_congr iff.rfl (xor_comm q r)).mp
      ... → xor (xor r q) p : (xor_comm p (xor r q)).mp
      ... → xor r (xor q p) : xor_assoc_impl r q p
      ... → xor r (xor p q) : (xor_congr iff.rfl (xor_comm q p)).mp
      ... → xor (xor p q) r : (xor_comm r (xor p q)).mp
}

#print axioms xor_assoc
