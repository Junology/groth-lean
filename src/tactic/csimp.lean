namespace tactic
namespace interactive

open tactic interactive lean.parser interactive.types

local postfix `?`:9001 := optional
local postfix *:9001 := many

--- Conservative analogue of `simp`; it is the same as `simp` except that it does not use any axioms.
meta def csimp (use_iota_eqn : parse $ (tk "!")?) (trace_lemmas : parse $ (tk "?")?)
  (no_dflt : parse only_flag) (hs : parse simp_arg_list) (attr_names : parse with_ident_list)
  (locat : parse location) (cfg : simp_config_ext := {use_axioms := ff}) : tactic unit :=
simp use_iota_eqn trace_lemmas no_dflt hs attr_names locat cfg

end interactive
end tactic
