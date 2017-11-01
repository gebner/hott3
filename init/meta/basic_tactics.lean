/-
Copyright (c) 2017 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

namespace tactic

open expr
variable {elab : bool}

/-- returns a list of domains (in reverse order) and the conclusion of the expression -/
meta def destruct_pis : expr elab → list (expr elab) × expr elab
| (pi _ _ a b) := let (es, e) := destruct_pis b in (a::es, e)
| a         := ([], a)

open interaction_monad interaction_monad.result
meta def change_failure {α : Type _} (t₁ : tactic α) (t₂ : format → format) : tactic α :=
λ s, match t₁ s with
| (exception (some f) pos s') := exception (some (t₂ ∘ f)) pos s' 
| (exception none pos s') := exception none pos s'
| (interaction_monad.result.success a s') := interaction_monad.result.success a s'
end

open interaction_monad interaction_monad.result
meta def trace_failure {α : Type _} (t₁ : tactic α) : tactic α :=
λ s, match t₁ s with
| (exception (some f) pos s') := (trace (f ()) >> exception none pos) s' 
| (exception none pos s') := exception none pos s'
| (interaction_monad.result.success a s') := interaction_monad.result.success a s'
end

namespace interactive

open lean lean.parser interactive
local postfix `?`:9001 := optional

meta def fconstructor : tactic unit :=
tactic.fconstructor

meta def infer : tactic unit := apply_instance

private meta def generalize_arg_p : pexpr → parser (pexpr × name)
| (app (app (macro _ [const `hott.eq _ ]) h) (local_const x _ _ _)) := pure (h, x)
| _ := fail "parse error"

meta def hgeneralize (h : parse ident?) (p : parse $ tk ":" *> with_desc "expr = id" (parser.pexpr 0 >>= generalize_arg_p)) : tactic unit :=
tactic.interactive.generalize h p

meta def trace_failure : itactic → tactic unit :=
tactic.trace_failure

end interactive
end tactic
