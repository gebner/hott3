/-
Copyright (c) 2017 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

namespace tactic
namespace interactive

open lean lean.parser interactive expr
local postfix `?`:9001 := optional

meta def fconstructor : tactic unit :=
tactic.fconstructor

meta def infer : tactic unit := apply_instance

private meta def generalize_arg_p : pexpr → parser (pexpr × name)
| (app (app (macro _ [const `hott.eq _ ]) h) (local_const x _ _ _)) := pure (h, x)
| _ := fail "parse error"

meta def hgeneralize (h : parse ident?) (p : parse $ tk ":" *> with_desc "expr = id" (parser.pexpr 0 >>= generalize_arg_p)) : tactic unit :=
tactic.interactive.generalize h p

end interactive
end tactic
