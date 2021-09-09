import logic.definite_description

/-=========================
 == Functional relations ==
 ==========================-/

--- Definition of functional relations
structure {u v} funrel (α : Sort u) (β : Sort v) : Sort (max u v+1) :=
  mk :: (p : α → β → Prop) (huniq : ∀ (a : α), ∃! (b : β), p a b)

reserve infixr `⇒`:1
infixr `⇒` := funrel

namespace funrel

--- Equivalent functional relations
definition equiv {α : Sort _} {β : Sort _} (f f': α ⇒ β) : Prop :=
  ∀ a b, f.p a b ↔ f'.p a b

--- Functional relations arise from actual functions; i.e. as the graph of functions.
definition from_fun {α : Sort _} {β : Sort _} : (α → β) → (α ⇒ β) :=
  λ f, funrel.mk (λ a b, f a = b)
    begin
      intro a,
      apply exists_unique.intro,
      show β, by exact (f a),
      reflexivity,
      exact @eq.symm β (f a)
    end

--- Identity functional relation
definition id {α : Sort _} : α ⇒ α :=
  funrel.mk eq
    begin
      intro a,
      apply exists_unique.intro; try {trivial},
      exact @eq.symm α a
    end

--- Compose an ambiguous-valued function with a functional relation when the result is unambigous.
definition unambiguous_comp {α : Sort _} {β : Sort _} {γ : Sort _} (fp : α → β → Prop) (fhex : ∀ a, ∃ b, fp a b) (g : β ⇒ γ) (hcoeq : ∀ a b b' c c', fp a b → fp a b' → g.p b c → g.p b' c' → c=c') : α ⇒ γ :=
  funrel.mk (λ a c, ∃ b, fp a b ∧ g.p b c)
    begin
      intro a,
      cases fhex a with b hb,
      apply exists_unique.elim (g.huniq b),
      intros c hc _,
      apply exists_unique.intro,
      show γ,
        by exact c,
      show ∃ (b : β), fp a b ∧ g.p b c,
        by exact ⟨b, and.intro hb hc⟩,
      show ∀ (y : γ), (∃ (b : β), fp a b ∧ g.p b y) → y = c, {
        intros c' hcomp,
        cases hcomp with b' hb',
        exact hcoeq a b' b c' c hb'.left hb hb'.right hc
      }
    end

--- Composition of functional relations
definition comp {α β γ : Sort _} (g : β ⇒ γ) (f : α ⇒ β) : (α ⇒ γ) :=
  begin
    apply unambiguous_comp f.p (λ a, exists_of_exists_unique (f.huniq a)) g,
    show ∀ (a : α) (b b' : β) (c c' : γ), f.p a b → f.p a b' → g.p b c → g.p b' c' → c = c', {
      intros a b b' c c' hb hb' hc hc',
      have : b=b',
        by exact unique_of_exists_unique (f.huniq a) hb hb',
      cases this,
      show c=c',
        by exact unique_of_exists_unique (g.huniq b) hc hc'
    }
  end

--- Eliminating invariant parameters
definition invariant {θ : Type*} {α β : Sort _} [ht : nonempty θ] (f : θ → (α ⇒ β)) (hf : ∀ t₁ t₂, equiv (f t₁) (f t₂)) : Σ' (g : α ⇒ β), (∀ t, equiv (f t) g) :=
  begin
    apply psigma.mk,
    show (α⇒β), {
      apply funrel.mk (λ a b, ∃ t, (f t).p a b),
      apply nonempty.elim ht,
      intros t a,
      apply exists_unique.elim ((f t).huniq a),
      intros b hb hbuniq,
      apply exists_unique.intro b (Exists.intro t hb),
      intros b' ht,
      cases ht with t' ht',
      have : (f t).p a b', by exact (hf t' t a b').mp ht',
      exact unique_of_exists_unique ((f t).huniq a) this hb
    },
    simp [equiv],
    intros t a b,
    apply iff.intro,
    show (f t).p a b → (∃ (t : θ), (f t).p a b),
      by exact λ h, ⟨t,h⟩,
    show (∃ (t : θ), (f t).p a b) → (f t).p a b, {
      intro tex,
      cases tex with t' ht',
      exact (hf t' t a b).mp ht'
    }
  end

--- Analogue of injectivity
definition injective {α : Sort _} {β : Sort _} : funrel α β → Prop :=
  λ f, ∀ (a1 a2 : α) (b : β), f.p a1 b → f.p a2 b → a1=a2

--- Analogue of surjectivity
definition surjective {α : Sort _} {β : Sort _} : funrel α β → Prop :=
  λ f, ∀ (b : β), ∃ (a : α), f.p a b

--- "Invertible" functional relations
definition isom {α : Sort _} {β : Sort _} : funrel α β → Prop :=
  λ f, ∀ (b : β), ∃! (a : α), f.p a b

--- Inverse of an invertible functional relation
definition inverse {α β : Sort _} (f : α ⇒ β) (hisom : isom f) : β ⇒ α :=
{
  p := λ b a, f.p a b,
  huniq := hisom
}

--- Bijective functions define invertible functional relations
theorem bijective_fun_isom {α : Sort _} {β : Sort _} {f : α → β} (hbij : function.bijective f) : isom (from_fun f) :=
  begin
    intro b,
    cases hbij.right b with a ha,
    existsi a; split; try {exact ha},
    intros a',
    dsimp [from_fun],
    rw [← ha],
    apply hbij.left
  end

#print axioms bijective_fun_isom

definition inverse_of_bijective {α β : Sort _} {f : α → β} (hbij : function.bijective f) : β ⇒ α :=
  inverse (from_fun f) (bijective_fun_isom hbij)

/-!
 - Invariance of functions
 -/
--- Existence of an element with a specific property and uniqueness up to a relation.
structure exists_unique_upto {α : Sort _} (p : α → Prop) (r : α → α → Prop) : Prop :=
  intro :: (hexists : ∃ (a : α), p a) (hinv : ∀ a a', p a → p a' → r a a')

local notation `∃[`:1024 r `]`:1024 binders `%:`:0 t:(scoped p, exists_unique_upto p r) := t

--- Coequalize a "pre"-function that is ambiguous up to a relation.
definition deambiguate_comp_rel {α β γ : Sort _} {fp : α → β → Prop} {r : β → β → Prop} (fhuniq : ∀ (a : α), ∃[r](b:β)%: fp a b) (g : β ⇒ γ) (hcoeq : ∀ b b' c c', r b b' → g.p b c → g.p b' c' → c=c') : α ⇒ γ :=
  funrel.mk (λ a c, ∃ b, fp a b ∧ g.p b c)
    begin
      intros a,
      cases fhuniq a with hex hinv,
      cases hex with b hb,
      cases g.huniq b with c hc,
      apply exists_unique.intro,
      show γ, by exact c,
      show ∃ (b : β), fp a b ∧ g.p b c, {
        by exact ⟨b, and.intro hb hc.left⟩
      },
      show ∀ (y : γ), (∃ (b : β), fp a b ∧ g.p b y) → y = c, {
        intros c' hcomp,
        cases hcomp with b' hb',
        have : r b' b, by exact hinv b' b hb'.left hb,
        apply hcoeq b' b c' c this hb'.right hc.left
      }
    end

/-!
 - Correspondence between functional relations and functions.
 - This requires `definite_description` axiom.
 - Consequence: functional relations can be seen as actual functions under `definite_description` and functional extensionality; e.g. in a Grothendieck topos.
 -/
namespace unsafe

--- Realize a function from a functional_relation
noncomputable definition reify {α β : Sort _} : (α ⇒ β) → α → β :=
  λ f a, (definite_description (f.huniq a)).val

--- It is a guaranteed that the values of `reify f` is the "right" one.
lemma reify_property {α β : Sort _} (f : α ⇒ β) : ∀ {a}, f.p a (reify f a) :=
  λ a, (definite_description (f.huniq a)).property

--- Computation rule for `reify`.
lemma reify_eq {α β : Sort _} (f : α ⇒ β) : ∀ {a b}, f.p a b ↔ reify f a = b :=
  begin
    intros a b,
    split,
    show f.p a b → reify f a = b, {
      intro hab,
      cases f.huniq a with b₀ hb,
      have : b = b₀ := hb.right b hab,
      rw [this],
      apply hb.right,
      exact reify_property f
    },
    show reify f a = b → f.p a b, {
      intros hab,
      rw [←hab],
      exact reify_property f
    },
  end

#print axioms reify_eq

--- Realization of an injective functional relation is injective.
lemma reify_injective {α β : Sort _} (f : α ⇒ β) (hinj : injective f) : function.injective (reify f) :=
  begin
    intros a b hfab,
    have hfa : f.p a (reify f b) := (reify_eq f).mpr hfab,
    have hfb : f.p b (reify f b) := reify_property f,
    exact hinj a b _ hfa hfb
  end

--- Realization of a surjective functional relation is surjective.
lemma reify_surjective {α β : Sort _} (f : α ⇒ β) (hsurj : surjective f) : function.surjective (reify f) :=
  begin
    intros b,
    cases hsurj b with a ha,
    existsi a,
    exact (reify_eq f).mp ha
  end

--- Realization of an inverse of an invertible functional relation is an inverse.
lemma reify_inverse {α β : Sort _} {f : α ⇒ β} (hisom : isom f) : (∀ a, reify (inverse f hisom) (reify f a) = a) ∧ (∀ b, reify f (reify (inverse f hisom) b) = b) :=
  begin
    split,
    show ∀ a, reify (inverse f hisom) (reify f a) = a, {
      intros a,
      apply (reify_eq _).mp,
      dsimp [inverse],
      exact reify_property f
    },
    show ∀ b, reify f (reify (inverse f hisom) b) = b, {
      intros b,
      apply (reify_eq _).mp,
      exact reify_property (inverse f hisom)
    }
  end

--- functions are recovered via functional relations
theorem reify_fun_id {α β : Sort _} (f : α → β) : ∀ (a : α), reify (from_fun f) a = f a :=
  begin
    intro a,
    simp [reify, coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe, coe_b, has_coe.coe],
    let x := definite_description ((from_fun f).huniq a),
    rw (@rfl β x.val),
    exact eq.symm x.property
  end

--- functional relations are recovered via functions
theorem fun_reify_id {α β : Sort _} (f : α ⇒ β) : ∀ (a : α) (b : β), (from_fun (reify f)).p a b ↔ f.p a b :=
  begin
    intros a b,
    apply iff.intro,
    show (from_fun (reify f)).p a b → f.p a b, {
      intro h,
      have : reify f a = b, by exact h,
      rw [←this],
      simp [reify, coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe, coe_b, has_coe.coe],
      exact (definite_description (f.huniq a)).property
    },
    show f.p a b → (from_fun (reify f)).p a b, {
      intro h,
      unfold from_fun,
      suffices hs : reify f a = b, by exact hs,
      simp [reify, coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe, coe_b, has_coe.coe],
      apply unique_of_exists_unique (f.huniq a),
      show f.p a b, by assumption,
      let x := definite_description (f.huniq a),
      exact x.property
    }
  end
end unsafe

end funrel
