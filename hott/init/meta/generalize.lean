/-
Copyright (c) 2017 Gabriel Ebner, Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich
-/
import hott.init.path
open tactic expr

hott_theory

namespace tactic.interactive
open lean lean.parser interactive interactive.types

private meta def generalize_arg_p : pexpr → parser (pexpr × name)
| (app (app _ h) (local_const x _ _ _)) := pure (h, x)
| _ := fail "cannot parse argument to hgeneralize"

/-- `hgeneralize : e = x` replaces all occurrences of `e` in the target with a new hypothesis `x` of the same type.
    `hgeneralize h : e = x` in addition registers the hypothesis `h : e = x`. -/
meta def hgeneralize (h : parse (optional ident)) (p : parse $ tk ":" *> with_desc "expr = id" (parser.pexpr 0 >>= generalize_arg_p)) : tactic unit :=
do let (p, x) := p,
   e ← i_to_expr p,
   some h ← pure h | tactic.generalize e x >> intro1 >> skip,
   tgt ← target,
   -- if generalizing fails, fall back to not replacing anything
   tgt' ← do {
     ⟨tgt', _⟩ ← solve_aux tgt (tactic.generalize e x >> target),
     to_expr ``(Π x, %%e = x → %%(tgt'.binding_body.lift_vars 0 1))
   } <|> to_expr ``(Π x, %%e = x → %%tgt),
   t ← assert h tgt',
   swap,
   exact ``(%%t %%e idp),
   intro x,
   intro h

end tactic.interactive