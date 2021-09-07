import data.vect.basic
import tactic.csimp

universes u v

-- Tree of operators
inductive optree (op : ℕ → Type u) (α : Type v) : Type.{max u v}
| varleaf {} (a : α) : optree
| opnode {n : ℕ} (f : op n) : vect optree n → optree

notation `⦃`:1024 f ` | ` t:(foldr `, ` (e r, vect.cons e r) vect.nil `⦄`) := optree.opnode f t

prefix `◎`:100 := optree.varleaf

namespace optree

/-**********************************-
 - Well-founded recursion on optree
 -**********************************-/

-- Check if the second argument is a parent of the first
definition is_child {op : ℕ → Type*} {α : Type*} : optree op α → optree op α → Prop
| t (varleaf _) := false
| t (opnode f sub) := sub.mem t

-- Count the number of nods
mutual definition nnodes, nnodes_vec
with nnodes : Π{op : ℕ → Type*}, Π{α : Type*}, optree op α → ℕ
| _ _ (varleaf _) := 0
| _ _ (opnode f vect.nil) := 1
| _ _ (opnode f (vect.cons x xs)) := nnodes x + nnodes_vec xs + 1
with nnodes_vec : Π{op : ℕ → Type*}, Π {α : Type*}, Π {n : ℕ}, vect (optree op α) n → ℕ
| _ _ _ vect.nil := 0
| _ _ _ (vect.cons x xs) := nnodes x + nnodes_vec xs

-- Well-founded recursion based on the number of nodes
definition nnodes_wf {op : ℕ → Type*} {α : Type*} :=
  measure_wf (@nnodes op α)

-- Auxiliary function to define nnodes_child
theorem nnodes_vec_mem {op : ℕ → Type*} {α : Type*} (tm : optree op α) {n : ℕ} (ts : vect (optree op α) n) : ts.mem tm → nnodes tm ≤ nnodes_vec ts:=
  begin
    induction ts with n ts_head ts_tail h_ind,
    case vect.nil {
      exact false.elim
    },
    case vect.cons {
      simp [vect.mem,nnodes_vec],
      intro hmem,
      cases hmem,
      case or.inl {
        rw [hmem],
        exact nat.le_add_right tm.nnodes (nnodes_vec ts_tail)
      },
      case or.inr {
        by calc
          tm.nnodes
              ≤ nnodes_vec ts_tail : h_ind hmem
          ... ≤ ts_head.nnodes + nnodes_vec ts_tail : nat.le_add_left _ _
      }
    }
  end

-- If a tree is a child of another, then the number of nodes decreases
theorem nnodes_child {op : ℕ → Type*} {α : Type*} (tc tp : optree op α) : is_child tc tp → nnodes tc < nnodes tp :=
  begin
    intros hchild,
    cases tp with _ n f ts,
    case optree.varleaf { exact false.elim hchild },
    unfold is_child at hchild,
    cases ts with n t ts,
    case vect.nil {
      exact false.elim hchild
    },
    case vect.cons {
      unfold nnodes,
      unfold vect.mem at hchild,
      cases hchild,
      case or.inl {
        rw [hchild],
        by calc
          tc.nnodes
              ≤ tc.nnodes + nnodes_vec ts : nat.le_add_right _ _
          ... < tc.nnodes + nnodes_vec ts + 1
                : nat.lt_add_of_pos_right (nat.succ_pos 0)
      },
      case or.inr {
        by calc
          tc.nnodes
              ≤ nnodes_vec ts : nnodes_vec_mem tc ts hchild
          ... ≤ t.nnodes + nnodes_vec ts : nat.le_add_left _ _
          ... < t.nnodes + nnodes_vec ts + 1
                : nat.lt_add_of_pos_right (nat.succ_pos 0)
      }
    }
  end

-- Accessibility for optree
theorem accessible {op : ℕ → Type*} {α : Type*}: ∀ {t : optree op α}, acc is_child t :=
  begin
    intro t,
    apply nnodes_wf.fix,
    intros x h_ind,
    clear t,
    simp [measure, inv_image] at h_ind,
    apply acc.intro,
    intros y hchild,
    exact h_ind y (nnodes_child y x hchild)
  end

-- Well-founded recursion based on the parent-children relation.
definition children_wf {op : ℕ → Type*} {α : Type*} : well_founded (@is_child op α) :=
  well_founded.intro (@accessible op α)


/-************************-
 - Basic operations
 -************************-/
-- Mapping on variables
mutual definition map , map_aux {op : ℕ → Type*} {α : Type*} {β : Type*} (f : α → β)
with map : optree op α → optree op β
| (varleaf a) := varleaf (f a)
| (opnode g vect.nil) := opnode g vect.nil
| (opnode g (vect.cons x xs)) := opnode g (vect.cons (map x) (map_aux xs))
with map_aux : Π{n : ℕ}, vect (optree op α) n → vect (optree op β) n
| _ vect.nil := vect.nil
| _ (vect.cons x xs) := vect.cons (map x) (map_aux xs)

-- Join 2-fold trees
mutual definition join, join_aux {op : ℕ → Type*} {α : Type*}
with join : optree op (optree op α) → optree op α
| (varleaf t) := t
| (opnode g vect.nil) := opnode g vect.nil
| (opnode g (vect.cons x xs)) := opnode g (vect.cons (join x) (join_aux xs))
with join_aux : Π{n : ℕ}, vect (optree op (optree op α)) n → vect (optree op α) n
| _ vect.nil := vect.nil
| _ (vect.cons t ts) := vect.cons (join t) (join_aux ts)

-- Eliminator
mutual definition elim, elim_aux {op : ℕ → Type*} {α : Type*} {β : Type*} (act : Π {n : ℕ}, op n → vect β n → β) (c : α → β)
with elim : optree op α → β
| (varleaf a) := c a
| (opnode f vect.nil) := act f vect.nil
| (opnode f (vect.cons t ts)) := act f (vect.cons (elim t) (elim_aux ts))
with elim_aux : Π{n : ℕ}, vect (optree op α) n → vect β n
| _ vect.nil := vect.nil
| _ (vect.cons t ts) := vect.cons (elim t) (elim_aux ts)

-- Unzipping pairs of variables into the same shape of trees
/-
definition unzip {op : ℕ → Type.{u}} {α : Type.{v}} {β : Type.{w}} : optree op (α×β) → optree op α × optree op β :=
  λ t, t.elim
    (λ _ f xs, (opnode f xs.unzip.fst, opnode f xs.unzip.snd))
    (λ (x : α×β), (optree.varleaf x.fst, optree.varleaf x.snd))
-/
mutual definition unzip, unzip_aux {op : ℕ → Type*} {α : Type*} {β : Type*}
with unzip : optree op (α×β) → optree op α × optree op β
| (varleaf t) := (varleaf t.fst, varleaf t.snd)
| (opnode f vect.nil) := (opnode f vect.nil, opnode f vect.nil)
| (opnode f (vect.cons t ts)) := (opnode f (vect.cons (unzip t).fst (unzip_aux ts).fst), opnode f (vect.cons (unzip t).snd (unzip_aux ts).snd))
with unzip_aux : Π{n : ℕ}, vect (optree op (α×β)) n → vect (optree op α) n × vect (optree op β) n
| _ vect.nil := (vect.nil, vect.nil)
| _ (vect.cons t ts) := (vect.cons (unzip t).fst (unzip_aux ts).fst, vect.cons (unzip t).snd (unzip_aux ts).snd)


/-***********************-
 - Basic properties
 -***********************-/
-- "Non-homogeneous" injectivity of opnode
theorem opnode_inj_nh {op : ℕ → Type*} {α : Type*} : Π {n : ℕ} {f1 f2 : op n} {t1 t2 : vect (optree op α) n}, opnode f1 t1 = opnode f2 t2 → f1=f2 ∧ t1=t2 :=
  begin
    intros n f1 f2 t1 t2 h,
    cases (opnode.inj h).right.left,
    cases (opnode.inj h).right.right,
    split; refl
  end

-- Differenti constructors produce different terms
theorem varleaf_neq_opnode {op : ℕ → Type*} {α : Type*} : ∀ {a : α} {n : ℕ} {f : op n} {t : vect (optree op α) n}, varleaf a ≠ opnode f t :=
  begin
    intros,
    simp *
  end

-- Functoriality
mutual theorem map_comp, map_aux_comp {op : ℕ → Type*} {α : Type*} {β : Type*} {γ : Type*} {g : β → γ} {f : α → β}
with map_comp : ∀ (t : optree op α), map (g∘f) t = map g (map f t)
| (varleaf _) := by unfold map; refl
| (opnode _ vect.nil) := by unfold map
| (opnode _ (vect.cons t ts)) :=
  begin
    unfold map,
    rw [map_comp t, map_aux_comp ts]
  end
with map_aux_comp : ∀ {n : ℕ} (ts : vect (optree op α) n), map_aux (g∘f) ts = map_aux g (map_aux f ts)
| _ vect.nil := by unfold map_aux; refl
| _ (vect.cons t ts) :=
  begin
    unfold map_aux,
    rw [map_comp t, map_aux_comp ts]
  end

-- Left unitalities of join; i.e. eT = id
theorem join_unit_outer {op : ℕ → Type*} {α : Type*} : ∀ {t : optree op α}, join (varleaf t) = t :=
  λ t, by unfold join

-- Right unitality of join; i.e. Te = id
mutual theorem join_unit_inner, join_aux_unit_inner {op : ℕ → Type*} {α : Type*}
with join_unit_inner : ∀ {t : optree op α}, join (map optree.varleaf t) = t
| (varleaf a) := by unfold map; unfold join
| (opnode f vect.nil) := by unfold map; unfold join
| (opnode f (vect.cons t ts)) :=
  begin
    simp [map,join],
    rw[join_unit_inner, join_aux_unit_inner],
    try {split; refl}
  end
with join_aux_unit_inner : ∀ {n : ℕ} {ts : vect (optree op α) n}, join_aux (map_aux optree.varleaf ts) = ts
| _ vect.nil := by simp [map_aux,join_aux]; refl
| _ (vect.cons t ts) :=
  begin
    simp [map_aux,join_aux],
    split,
    show (map varleaf t).join = t,
      from join_unit_inner,
    show join_aux (map_aux varleaf ts) = ts,
      from join_aux_unit_inner
  end

-- Associativity of join
mutual theorem join_assoc, join_aux_assoc {op : ℕ → Type*} {α : Type*}
with join_assoc : ∀ {t : optree op (optree op (optree op α))}, join (join t) = join (map join t)
| (varleaf _) := by simp [map, join]
| (opnode _ vect.nil) := by simp [map, join]; try {split; refl}
| (opnode _ (vect.cons t ts)) :=
  begin
    simp [map, join],
    rw [join_assoc, join_aux_assoc],
    try {split; refl}
  end
with join_aux_assoc : ∀ {n : ℕ} {ts : vect (optree op (optree op (optree op α))) n}, join_aux (join_aux ts) = join_aux (map_aux join ts)
| _ vect.nil := by simp [map_aux, join_aux]; refl
| _ (vect.cons t ts) :=
  begin
    simp [map_aux, join_aux],
    split,
    show join (join t) = join (map join t),
      from join_assoc,
    show join_aux (join_aux ts) = join_aux (map_aux join ts),
      from join_aux_assoc
  end

-- elim_aux is equivalent to map elim
theorem elim_aux_map {op : ℕ → Type*} {α β : Type*} {act : Π {n : ℕ}, op n → vect β n → β} {c : α → β} : ∀ {n : ℕ} {ts : vect (optree op α) n}, elim_aux @act c ts = vect.map (elim @act c) ts
| _ vect.nil := by unfold elim_aux; unfold vect.map
| _ (vect.cons t ts) :=
  begin
    unfold elim_aux; unfold vect.map,
    rw [elim_aux_map]
  end

#print axioms elim_aux_map

-- The eliminator at varleaf
theorem elim_varleaf {op : ℕ → Type*} {α β : Type*} {act : Π {n : ℕ}, op n → vect β n → β} {c : α → β} : ∀ {a : α}, elim @act c (varleaf a) = c a :=
  by intros; unfold elim; refl

#print axioms elim_varleaf

-- The eliminator at opnode
theorem elim_opnode {op : ℕ → Type*} {α : Type*} {β : Type*} {act : Π {n : ℕ}, op n → vect β n → β} {c : α → β} : ∀ {n : ℕ} {f : op n} {ts : vect (optree op α) n}, elim @act c (opnode f ts) = act f (vect.map (elim @act c) ts)
| _ f vect.nil := by unfold elim; unfold vect.map
| _ f (vect.cons t ts) :=
  begin
    unfold elim; unfold vect.map,
    rw [elim_aux_map]
  end

#print axioms elim_opnode

--- `elim` followed by a function application equals `elim`.
mutual theorem elim_funap, elim_aux_funap {op : ℕ → Type*} {α β γ: Type*} {actb : Π {n : ℕ}, op n → vect β n → β} {actc : Π {n : ℕ}, op n → vect γ n → γ} {c : α → β} {f : β → γ} (hact : ∀ {n} (μ : op n) (bs : vect β n), f (actb μ bs) = actc μ (bs.map f))
with elim_funap : ∀ {t : optree op α}, f (t.elim @actb c) = t.elim @actc (f ∘ c)
| (varleaf x) := by unfold elim
| (opnode μ ⁅⁆) := by unfold elim; rw [hact]; dunfold vect.map; refl
| (opnode μ (t ∺ ts)) :=
  begin
    unfold elim,
    rw [hact],
    unfold vect.map,
    rw [elim_funap, elim_aux_funap]
  end
with elim_aux_funap : ∀ {n : ℕ} {ts : vect (optree op α) n}, vect.map f (elim_aux @actb c ts) = elim_aux @actc (f ∘ c) ts
| _ ⁅⁆ := by unfold elim_aux; unfold vect.map
| _ (t ∺ ts) := by unfold elim_aux; unfold vect.map; rw [elim_funap, elim_aux_funap]

#print axioms elim_funap

-- The eliminator respects function extensionality
mutual theorem elim_funext, elim_aux_funext {op : ℕ → Type*} {α : Type*} {β : Type*} {act₁ act₂ : Π {n : ℕ}, op n → vect β n → β} {c₁ c₂ : α → β} (hact : ∀ {n : ℕ} {f : op n} {bs : vect β n}, act₁ f bs = act₂ f bs) (hc : ∀ {a : α}, c₁ a = c₂ a)
with elim_funext : ∀ {t : optree op α}, elim @act₁ c₁ t = elim @act₂ c₂ t
| (varleaf x) := by unfold elim; exact hc
| (opnode f vect.nil) := by unfold elim; exact hact
| (opnode f (vect.cons t ts)) :=
  by unfold elim; rw [elim_funext,elim_aux_funext, hact]
with elim_aux_funext : ∀ {n : ℕ} {ts : vect (optree op α) n}, elim_aux @act₁ c₁ ts = elim_aux @act₂ c₂ ts
| _ vect.nil := by unfold elim_aux
| _ (vect.cons t ts) :=
  begin
    unfold elim_aux,
    rw [elim_funext,elim_aux_funext],
  end

#print axioms elim_funext

-- Elimination into pairs produces pairs of elimination
mutual theorem elim_prod, elim_aux_prod {op : ℕ → Type*} {α : Type*} {β₁ : Type _} {β₂ : Type _} {act₁ : Π {n : ℕ}, op n → vect β₁ n → β₁} {act₂ : Π {n : ℕ}, op n → vect β₂ n → β₂} (c : α → β₁×β₂)
with elim_prod : ∀ {t : optree op α}, t.elim (λ _ f, prod.map (act₁ f) (act₂ f) ∘ vect.unzip) c = (t.elim @act₁ (prod.fst∘c), t.elim @act₂ (prod.snd∘ c))
| (varleaf x) := by unfold elim; unfold function.comp; rw [prod.mk.eta]
| (opnode f vect.nil) := by unfold elim; unfold function.comp; unfold vect.unzip; unfold prod.map
| (opnode f (vect.cons t ts)) :=
  begin
    csimp [elim, vect.unzip, prod.map],
    rw [elim_prod, elim_aux_prod]
  end
with elim_aux_prod : ∀ {n : ℕ} {ts : vect (optree op α) n}, (@elim_aux op α (β₁×β₂) (λ _ f, prod.map (act₁ f) (act₂ f) ∘ vect.unzip) c n ts).unzip = (@elim_aux op α β₁ @act₁ (prod.fst∘c) n ts,@elim_aux op α β₂ @act₂ (prod.snd∘ c) n ts)
| _ vect.nil := by csimp [elim_aux, vect.unzip]
| _ (vect.cons t ts) :=
  begin
    csimp [elim_aux, vect.unzip, prod.map],
    rw [elim_prod, elim_aux_prod]
  end

#print axioms elim_prod

-- theorem elim_ext {op : ℕ → Type.{u}} {α : Type.{v}} {β : Type _} {B : β → Type _} {act : Π {n : ℕ}, op n → vect (Π b, B b) n → Π b, B b} {c : α → Π b, B b} := sorry

-- Elimination into pi-types produces pi of elimination
mutual theorem elim_pi, elim_aux_pi {op : ℕ → Type*} {α : Type*} {β : Type _} {B : β → Type _} {act : Π (b : β) {n : ℕ}, op n → vect (B b) n → B b} {c : Π b, α → B b}
with elim_pi : ∀ {t : optree op α} {b : β}, t.elim (λ k f ts, λ (b : β), @act b k f (ts.unzip_fam b)) (λ a b, c b a) b = t.elim (@act b) (c b)
| (varleaf x) b := by unfold elim
| (opnode f vect.nil) b := by unfold elim; unfold vect.unzip_fam
| (opnode f (vect.cons t ts)) b :=
  by unfold elim; unfold vect.unzip_fam; rw [elim_pi, elim_aux_pi]
with elim_aux_pi : ∀ {n : ℕ} {ts : vect (optree op α) n} {b : β}, (elim_aux (λ k f ts, λ (b : β), @act b k f (ts.unzip_fam b)) (λ a b, c b a) ts).unzip_fam b = elim_aux (@act b) (c b) ts
| _ vect.nil b := by unfold elim_aux; refl
| _ (vect.cons t ts) b :=
  begin
    unfold elim_aux; unfold vect.unzip_fam,
    apply congr; try {apply congr}; try {refl},
    rw [elim_pi],
    rw [elim_aux_pi]
  end

#print axioms elim_pi

mutual theorem elim_subtype, elim_aux_subtype {op : ℕ → Type*} {α : Type*} {β : Type _} {P : β → Prop} {act : Π {n : ℕ}, op n → vect β n → β} {hsub : ∀ {n : ℕ} (f : op n) (ts : vect (subtype P) n), P (act f (vect.map subtype.val ts))} {c : α → subtype P}
with elim_subtype : ∀ {t : optree op α}, subtype.val (elim (λ n k (rs : vect (subtype P) n), ⟨@act n k (vect.map subtype.val rs), hsub k rs⟩) c t) = elim @act (subtype.val ∘ c) t
| (varleaf x) := by unfold elim
| (opnode f vect.nil) := by unfold elim; unfold vect.map
| (opnode f (vect.cons t ts)) :=
  begin
    unfold elim; unfold vect.map; unfold subtype.val,
    rw [elim_subtype, elim_aux_subtype]
  end
with elim_aux_subtype : ∀ {n : ℕ} {ts : vect (optree op α) n}, vect.map subtype.val (elim_aux (λ n k (rs : vect (subtype P) n), ⟨@act n k (vect.map subtype.val rs), hsub k rs⟩) c ts) = elim_aux @act (subtype.val ∘ c) ts
| _ vect.nil := by unfold elim_aux; refl
| _ (vect.cons t ts) :=
  begin
    unfold elim_aux; unfold vect.map,
    rw [elim_subtype, elim_aux_subtype],
    try {split; refl}
  end

#print axioms elim_subtype

-- unzip is an injective function.
mutual theorem unzip_inj, unzip_aux_inj {op : ℕ → Type*} {α : Type*} {β : Type*}
with unzip_inj : ∀ {t1 t2 : optree op (α×β)}, t1.unzip = t2.unzip → t1 = t2
| (varleaf x) (varleaf y) heq :=
  begin
    suffices : x=y, by rw [this],
    cases x,
    cases y,
    unfold unzip at heq,
    unfold prod.fst at heq; unfold prod.snd at heq,
    let h := prod.mk.inj heq,
    rw [varleaf.inj h.left, varleaf.inj h.right]
  end
| (varleaf x) (opnode g vect.nil) heq :=
  begin
    unfold unzip at heq,
    have : varleaf x.fst = opnode g vect.nil,
      from (prod.mk.inj heq).left,
    cases this
  end
| (varleaf x) (opnode g (vect.cons y ys)) heq :=
  begin
    unfold unzip at heq,
    have : varleaf x.fst = opnode g _,
      from (prod.mk.inj heq).left,
    cases this
  end
| (opnode f vect.nil) (varleaf y) heq :=
  begin
    unfold unzip at heq,
    have : opnode f _ = varleaf y.fst,
      from (prod.mk.inj heq).left,
    cases this
  end
| (opnode f (vect.cons x xs)) (varleaf y) heq :=
  begin
    unfold unzip at heq,
    have : opnode f _ = varleaf y.fst,
      from (prod.mk.inj heq).left,
    cases this
  end
| (opnode f vect.nil) (opnode g vect.nil) heq :=
  begin
    unfold unzip at heq,
    have : f = g,
      from (opnode_inj_nh (prod.mk.inj heq).left).left,
    rw [this]
  end
| (opnode f vect.nil) (opnode g (vect.cons y ys)) heq :=
  by unfold unzip at heq; cases heq
| (opnode f (vect.cons x xs)) (opnode g vect.nil) heq :=
  by unfold unzip at heq; cases heq
| (opnode f (vect.cons x xs)) (opnode g (vect.cons y ys)) heq :=
  begin
    unfold unzip at heq,
    cases (opnode.inj ((prod.mk.inj heq).left)).left,
    cases (opnode_inj_nh ((prod.mk.inj heq).left)).left,
    have h_head : x = y, {
      apply unzip_inj,
      cases x.unzip with x_fst x_snd,
      cases y.unzip with y_fst y_snd,
      have h_fst : x_fst = y_fst,
        from (vect.cons.inj ((opnode_inj_nh ((prod.mk.inj heq).left)).right)).left,
      have h_snd : x_snd = y_snd,
        from (vect.cons.inj ((opnode_inj_nh ((prod.mk.inj heq).right)).right)).left,
      rw [h_fst,h_snd]
    },
    have h_tail : xs = ys, {
      apply unzip_aux_inj,
      cases unzip_aux xs with xs_fst xs_snd,
      cases unzip_aux ys with ys_fst ys_snd,
      have h_fst : xs_fst = ys_fst,
        from (vect.cons.inj ((opnode_inj_nh ((prod.mk.inj heq).left)).right)).right,
      have h_snd : xs_snd = ys_snd,
        from (vect.cons.inj ((opnode_inj_nh ((prod.mk.inj heq).right)).right)).right,
      rw [h_fst,h_snd]
    },
    rw [h_head, h_tail]
  end
with unzip_aux_inj : ∀{n : ℕ} {ts1 ts2 : vect (optree op (α×β)) n}, unzip_aux ts1 = unzip_aux ts2 → ts1 = ts2
| _ vect.nil vect.nil heq := by trivial
| _ (vect.cons t1 ts1) (vect.cons t2 ts2) heq :=
  begin
    unfold unzip_aux at heq,
    let h1 := vect.cons.inj ((prod.mk.inj heq).left),
    let h2 := vect.cons.inj ((prod.mk.inj heq).right),
    have ht : t1 = t2, {
      apply unzip_inj,
      cases t1.unzip with t1_fst t1_snd,
      cases t2.unzip with t2_fst t2_snd,
      unfold prod.fst at h1 h2,
      unfold prod.snd at h1 h2,
      rw [h1.left,h2.left]
    },
    have hts : ts1 = ts2, {
      apply unzip_aux_inj,
      cases unzip_aux ts1 with ts1_fst ts1_snd,
      cases unzip_aux ts2 with ts2_fst ts2_snd,
      dsimp [prod.fst,prod.snd] at h1 h2,
      rw [h1.right,h2.right]
    },
    rw [ht,hts]
  end

#print axioms optree.unzip_inj

end optree


