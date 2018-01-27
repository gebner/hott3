/-
Copyright (c) 2017 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import ..pathover .rewrite
universes u v w

namespace hott
hott_theory

@[hott] def eq.cases_helper {A : Type u} {a b : A} (x : a = b) (C : Sort v) :
(∀ b' : A, ∀ x' : a = b', ∀ hb : b = b', ∀ hx : x =[hb] x', C) → C :=
by induction x; intro h; apply h; refl

end hott

namespace hott
open tactic expr

meta def eq_cases (x : expr) : tactic unit := do
tgt ← target,
mk_mapp ``eq.cases_helper [none, none, none, x, tgt] >>= apply,
b' ← intro1, x' ← intro1, induction x',
hb ← intro1, try (induction hb),
hx ← intro1,
try (do hx' ← mk_app ``hott.eq.eq_of_pathover_idp [hx],
        hx't ← infer_type hx',
        hx' ← assertv `hx hx't hx',
        try (clear hx),
        try (rewrite_target hx'))

end hott

namespace tactic.interactive
open tactic lean lean.parser interactive interactive.types

meta def eq_cases (e : parse texpr) : tactic unit :=
i_to_expr e >>= hott.eq_cases

end tactic.interactive