/-
Copyright (c) 2017 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import hott.init.path
open tactic expr

namespace hott

meta def instantiate_with_metas : expr → tactic expr | e := do
t ← infer_type e >>= whnf,
if ¬t.is_pi then return e else do
x ← mk_meta_var t.binding_domain,
instantiate_with_metas (e.app x)

meta def rewrite_core (eqn : expr) (tgt : expr) : tactic (expr × expr × expr) := do
eqn ← instantiate_with_metas eqn,
`(@hott.eq %%A %%lhs %%rhs) ← infer_type eqn,
abs ← kabstract tgt lhs,
when ¬abs.has_var $ (do lhs ← pp lhs, tgt ← pp tgt,
    fail $ to_fmt "rewrite_core: could not find pattern" ++ format.line
        ++ "  " ++ lhs ++ format.line
        ++ to_fmt "in" ++ format.line
        ++ "  " ++ tgt),
return (abs.instantiate_var rhs, eqn, lam `x binder_info.default A abs)

meta def mk_eq_inv (eqn : expr) : tactic expr :=
mk_app `hott.eq.inverse [eqn]

meta def mk_eq_transport (motive eqn : expr) : tactic expr :=
mk_mapp `hott.eq.transport [none, motive, none, none, eqn]

meta def rewrite_tgt (eqn : expr) : tactic unit := do
tgt ← target,
(tgt', prf, motive) ← rewrite_core eqn tgt,
type_check motive <|> (do m ← pp motive, fail $
    to_fmt "rwr: motive does not type check\n" ++ m),
prf ← mk_eq_inv prf,
prf ← mk_eq_transport motive prf,
apply prf

end hott

namespace tactic.interactive
open interactive interactive.types

meta def rwr (eqns: parse pexpr_list_or_texpr) : tactic unit :=
(eqns.mmap' $ λ eqn, do
eqn ← i_to_expr eqn,
hott.rewrite_tgt eqn) >> try refl

end tactic.interactive