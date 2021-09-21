import function.misc
import function.bijection
import data.list.misc
import data.list.map_partial
import data.finord
import data.subtype.misc
import tactic.unirewrite
import .basic

namespace exhaustive_list

--- Forget proofs to exhibit an `exhaustive_list` on a subtype of `α` as a list of `α`.
@[reducible]
protected
definition underlying {α : Type _} {p : α → Prop} (l : exhaustive_list (subtype p)) : list α :=
  l.val.map subtype.val

protected
lemma underlying_nodup {α : Type _} {p : α → Prop} (l : exhaustive_list (subtype p)) : l.underlying.nodup :=
  begin
    dunfold exhaustive_list.underlying,
    apply list.nodup_map_of_nodup subtype.val_injective,
    exact l.property.left
  end

protected
lemma underlying_exhaustive {α : Type _} {p : α → Prop} (l : exhaustive_list (subtype p)) : ∀ x, p x → x ∈ l.underlying :=
  begin
    intros x hx,
    dunfold exhaustive_list.underlying,
    unirewrite x with (subtype.mk x hx).val,
    exact list.mem_map_of_mem _ _ (l.property.right _)
  end

protected
lemma underlying_mem_iff {α : Type _} {p : α → Prop} (l : exhaustive_list (subtype p)) : ∀ x, p x ↔ x ∈ l.underlying :=
  begin
    intros x,
    split,
    show p x → _,
      from l.underlying_exhaustive x,
    show _ → p x, {
      intros hx,
      dunfold exhaustive_list.underlying at hx,
      cases l.val.inverse_of_mem_map hx with w hw,
      rw [hw]; exact w.property
    }
  end

--- For every pair of `exhaustive_list`s of a subtype, they are the same underlying list up to permutations.
protected
lemma underlying_perm {α : Type _} {p : α → Prop} (l₁ l₂ : exhaustive_list (subtype p)) : list.perm l₁.underlying l₂.underlying :=
  list.perm.map subtype.val (l₁.perm l₂)

--- The empty list is exhaustive on empty subtypes.
protected
definition of_empty {α : Type _} {p : α → Prop} (h : ∀ a, ¬p a) : exhaustive_list (subtype p) :=
  subtype.mk [] $
    begin
      split; try { exact list.nodup.nil },
      intros x,
      exact false.elim (h x x.property)
    end

--- Every `exhaustive_list` on an empty subtype is `nil`.
protected
lemma is_empty {α : Type _} {p : α → Prop} (h : ∀ a, ¬p a) (l : exhaustive_list (subtype p)) : l.val = [] :=
  begin
    apply list.is_nil_of_no_mem,
    intros x,
    exfalso,
    exact h x.val x.property
  end

--- `exhaustive_list`s of two subtypes classified by eqiuvalent predicators can be translated to one another.
@[reducible]
protected
definition of_iff {α : Type _} {p q : α → Prop} (h : ∀ a, p a ↔ q a) (l : exhaustive_list (subtype p)) : exhaustive_list (subtype q) :=
  l.translate (bijection.subtype_equiv h).is_bijective

--- Equivalent condition translation of `exhaustive_list` does nothing on the underlying `list`.
protected
definition of_iff_underlying {α : Type _} {p q : α → Prop} {h : ∀ a, p a  ↔ q a} (l : exhaustive_list (subtype p)) : (l.of_iff h).underlying = l.underlying:=
  begin
    dsimp [
      exhaustive_list.of_iff,
      exhaustive_list.translate,
      bijection.subtype_equiv,
      exhaustive_list.underlying
    ],
    rw [list.map_map],
    exact list.map_equiv (by intros x; cases x; refl)
  end

--- If `α` has an `exhaustive_list`, then each decidable subtype of `α` does.
protected
definition restrict {α : Type _} (l : exhaustive_list α) (p : α → Prop) [decidable_pred p] : exhaustive_list (subtype p) :=
  subtype.mk (l.val.filter_to_subtype p) $
    begin
      split,
      exact list.nodup_map_partial_of_nodup (function.partial.coinj_inj) l.property.left,
      intros x,
      have hx : (function.partial.coinj p).is_defined_at x.val,
        from (function.partial.coinj_domain x.val).mpr x.property,
      have : x = (function.partial.coinj p).to_fun ⟨x.val,hx⟩, {
        symmetry,
        suffices : function.partial.coinj p x.val = some x,
          from (function.partial.coinj p).to_fun_value_of_eq this,
        cases hinjx : function.partial.coinj p x.val with y,
        exfalso; exact hx hinjx,
        dunfold function.partial.coinj at hinjx,
        rw [dif_pos x.property] at hinjx,
        apply congr_arg some; apply subtype.eq,
        let hyxval := congr_arg subtype.val (option.some.inj hinjx.symm),
        exact hyxval,
      },
      rw [this],
      refine list.mem_map_partial_of_mem _ _ _,
      exact l.property.right _
    end

--- `exhaustive_list.restrict` is nothing but `filter` on the underlying `list`.
protected
lemma restrict_underlying {α : Type _} (l : exhaustive_list α) {p : α → Prop} [decidable_pred p] : (l.restrict p).underlying = l.val.filter p :=
  begin
    dunfold exhaustive_list.underlying,
    dsimp [exhaustive_list.restrict],
    rw [list.val_of_filter_to_subtype]
  end

--- Restrict an `exhaustive_list` on a subtype to a smaller subtype.
protected
definition subrestrict {α : Type _} {p : α → Prop} (l : exhaustive_list (subtype p)) (q : α → Prop) [decidable_pred q] : exhaustive_list {x // p x ∧ q x} :=
  let l' := (l.restrict (q ∘ subtype.val))
  in l'.translate bijection.subtype_uncurry.is_bijective

--- `exhaustive_list.subrestrict` is nothing but `filter` on the underlying `list`.
protected
lemma subrestrict_underlying {α : Type _} {p : α → Prop} (l : exhaustive_list (subtype p)) {q : α → Prop} [decidable_pred q] : (l.subrestrict q).underlying = l.underlying.filter q :=
  begin
    dsimp [exhaustive_list.subrestrict],
    dsimp [exhaustive_list.translate],
    dsimp [bijection.subtype_uncurry],
    dsimp [exhaustive_list.underlying],
    dunfold exhaustive_list.restrict,
    rw [list.map_map]; dsimp *,
    dunfold function.comp; dsimp *,
    have : ∀ (x : {x : subtype p // q x.val}), x.val.val = (subtype.val ∘ subtype.val) x,
      by intros; refl,
    rw [list.map_equiv this]; dsimp *,
    rw [←list.map_map],
    rw [list.val_of_filter_to_subtype],
    rw [list.filter_of_map]
  end

--- Partitioning an `exhaustive_list α` with a decidable predicator `p : α → Prop`.
protected
definition partition {α : Type _} (p : α → Prop) [decidable_pred p] (l : exhaustive_list α) : exhaustive_list (subtype p) × exhaustive_list {x // ¬p x} :=
  (l.restrict p, l.restrict (not ∘ p))

--- Underlying lists of partitioned `exhaustive_list`.
protected
lemma partition_underlying {α : Type _} {p : α → Prop} [decidable_pred p] {l : exhaustive_list α} : (l.partition p).map exhaustive_list.underlying exhaustive_list.underlying = l.val.partition p :=
  begin
    dunfold exhaustive_list.partition,
    dunfold prod.map,
    repeat { rw [exhaustive_list.restrict_underlying] },
    rw [list.partition_eq_filter_filter]
  end

--- Partitioning an `exhaustive_list` on a subtype with a decidable predicator `p`.
protected
definition subpartition {α : Type _} {p : α → Prop} (l : exhaustive_list (subtype p)) (q : α → Prop) [decidable_pred q] : exhaustive_list {x // p x ∧ q x} × exhaustive_list {x // p x ∧ ¬q x} :=
  (l.subrestrict q, l.subrestrict (not ∘ q))

--- Underlying lists of partitioned `exhaustive_list`.
protected
lemma subpartition_underlying {α : Type _} {p : α → Prop} {l : exhaustive_list (subtype p)} {q : α → Prop} [decidable_pred q]: (l.subpartition q).map exhaustive_list.underlying exhaustive_list.underlying = l.underlying.partition q :=
  begin
    dunfold exhaustive_list.subpartition,
    dunfold prod.map,
    repeat { rw [exhaustive_list.subrestrict_underlying] },
    rw [list.partition_eq_filter_filter],
  end

--- If two subtypes respectively admit exhaustive lists, then so does their union.
protected
definition union {α : Type _} [decidable_eq α] {p q : α → Prop} (lp : exhaustive_list (subtype p)) (lq : exhaustive_list (subtype q)) : exhaustive_list {x // p x ∨ q x} :=
  subtype.mk
    (list.union (lp.val.map subtype.inl) (lq.val.map subtype.inr)) $
    begin
      split,
      show list.nodup _, {
        apply list.nodup_union,
        exact list.nodup_map_of_nodup subtype.relax_inj lp.property.left,
        exact list.nodup_map_of_nodup subtype.relax_inj lq.property.left,
      },
      show ∀ x, x ∈ _, {
        intros x,
        apply list.mem_union_iff.mp,
        cases x.property with hx hx,
        case or.inl /- p x.val -/ {
          left,
          have : x = subtype.inl ⟨x.val,hx⟩,
            by cases x; refl,
          rw [this],
          apply list.mem_map_of_mem _ _,
          exact lp.property.right _
        },
        case or.inr /- q x.val -/ {
          right,
          have : x = subtype.inr ⟨x.val,hx⟩,
            by cases x; refl,
          rw [this],
          apply list.mem_map_of_mem _ _,
          exact lq.property.right _
        },
      },
    end

--- The underlying list of `union` of `exhaustive_list`s.
protected
lemma union_underlying {α : Type _} [decidable_eq α] {p q : α → Prop} {lp : exhaustive_list (subtype p)} {lq : exhaustive_list (subtype q)} : (lp.union lq).underlying = lp.underlying ∪ lq.underlying :=
  begin
    cases lp; cases lq,
    dsimp [exhaustive_list.union, exhaustive_list.underlying],
    drefold @has_union.union (list {x // p x ∨ q x}) _,
    rw [list.union_of_map_inj (@subtype.val_injective α _)],
    rw [list.map_map, list.map_map],
    rw [list.map_equiv subtype.val_inl],
    rw [list.map_equiv subtype.val_inr]
  end

--- The underlying list of `union` of `exhaustive_list`s for two subtypes are disjoint.
protected
lemma disjoint_union_underlying {α : Type _} [decidable_eq α] {p q : α → Prop} {lp : exhaustive_list (subtype p)} {lq : exhaustive_list (subtype q)} : (∀ x, ¬(p x ∧ q x)) → (lp.union lq).underlying = lp.underlying ++ lq.underlying :=
  begin
    intros hnpq,
    rw [exhaustive_list.union_underlying],
    apply list.nodup.disjoint_union lp.underlying_nodup,
    intros x hlpx hlqx,
    have hpx : p x,
      from (lp.underlying_mem_iff x).mpr hlpx,
    have hqx : q x,
      from (lq.underlying_mem_iff x).mpr hlqx,
    exact hnpq x ⟨hpx,hqx⟩
  end

end exhaustive_list

namespace is_finite

--- Empty subtype is finite
definition of_empty {α : Type _} {p : α → Prop} (h : ∀ x, ¬p x) : is_finite {x // p x} :=
  begin
    constructor,
    existsi 0,
    existsi (λ x, false.elim $ finord.zero_empty x),
    split,
    show function.injective _, {
      intros x,
      exfalso; exact finord.zero_empty x,
    },
    show function.surjective _, {
      intros x,
      exfalso; exact h x.val x.property
    }
  end

--- Decidable subtypes of a finite type is finite.
instance of_subtype {α : Type _} [decidable_eq α] [is_finite α] {p : α → Prop} [decidable_pred p] : is_finite (subtype p) :=
  begin
    cases has_exhaustive_list α with l,
    exact is_finite.of_exhaustive_list (l.restrict p)
  end

--- If a subtype is finite, then every equivalent subtype is also finite.
protected
lemma of_iff {α : Type _} [decidable_eq α] {p q : α → Prop} (hpq : ∀ x, p x ↔ q x) : is_finite (subtype p) → is_finite (subtype q) :=
  begin
    intros hp; cases @has_exhaustive_list _ hp with lp,
    exact is_finite.of_exhaustive_list (lp.of_iff hpq),
  end

--- Decidable subtype of a finite subtype is a finite subtype.
lemma of_subrestrict {α : Type _} [decidable_eq α] {p : α → Prop} : is_finite (subtype p) → Π (q : α → Prop) [decidable_pred q], is_finite {x // p x ∧ q x} :=
  begin
    intros hp; cases @has_exhaustive_list _ hp with lp,
    intros q hdec,
    apply is_finite.of_exhaustive_list,
    exact @exhaustive_list.subrestrict _ _ lp q hdec
  end

--- The union of finite subtypes is finite
lemma of_union {α : Type _} [decidable_eq α] {p q : α → Prop} : is_finite (subtype p) → is_finite (subtype q) → is_finite {x // p x ∨ q x} :=
  begin
    intro hp; cases @has_exhaustive_list _ hp with lp,
    intro hq; cases @has_exhaustive_list _ hq with lq,
    exact is_finite.of_exhaustive_list (lp.union lq)
  end

end is_finite
