namespace expr

meta definition find_head_name : expr → option name
| (const n _) := some n
| (local_const n _ _ _) := some n
| (app e _) := find_head_name e
| _ := none

end expr

namespace tactic.interactive

open lean.parser (tk)

open interactive
open interactive.types

meta definition unirewrite_core (e_pat e_tgt : expr) (lcs : parse location) : tactic unit := do
  tactic.unify e_pat e_tgt,
  e_eq ← tactic.i_to_expr ``(%%e_pat = %%e_tgt),
  e_prf ← tactic.i_to_expr ``(rfl : %%e_pat = %%e_tgt),
  nm ← tactic.mk_fresh_name,
  heq ← tactic.assertv nm e_eq e_prf,
  rule ← lean.parser.run $
    tactic.interactive.rw_rule.mk <$>
      lean.parser.cur_pos <*> pure ff <*> pure ``(%%heq),
  pos ← lean.parser.run $ lean.parser.cur_pos,
  tactic.interactive.rewrite ⟨[rule],pos⟩ lcs,
  tactic.clear heq
  -- tactic.clear heq
  <|> tactic.fail (
    "Failed to unify '"
    ++ to_string e_pat
    ++ "' with '"
    ++ to_string e_tgt ++ "'."
  )

--- `unirewrite x with y` behaves like `rw [rfl]` when expressions `x` and `y` are unified.
meta definition unirewrite (pat : parse texpr) (tgt : parse (tk "with" *> texpr)) (lcs : parse location) : tactic unit := do
  e_pat ← tactic.i_to_expr pat,
  e_tgt ← tactic.i_to_expr tgt,
  unirewrite_core e_pat e_tgt lcs

--- Converse to `dunfold`.
meta definition drefold (f : parse texpr) : parse location → tactic unit :=
  λ lcs, do
    e ← tactic.i_to_expr f,
    nm ← option.get_or_else
      (pure e.find_head_name)
      (tactic.fail "Not a function expression"),
    e_ff ← tactic.dunfold [nm] e {},
    unirewrite_core e_ff e lcs

end tactic.interactive
