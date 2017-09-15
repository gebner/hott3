/-
Copyright (c) 2017 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import ..path
open tactic expr

namespace hott

meta def instantiate_with_metas : expr → tactic expr | e := do
t ← infer_type e >>= whnf,
if ¬t.is_pi then return e else do
x ← mk_meta_var t.binding_domain,
instantiate_with_metas (e.app x)

meta def mk_eq_inv (eqn : expr) : tactic expr :=
mk_app `hott.eq.inverse [eqn]

meta def rewrite_core (eqn : expr) (tgt : expr) (cfg : rewrite_cfg) : tactic (expr × expr × expr) := do
eqn ← instantiate_with_metas eqn,
eqn ← if cfg.symm then mk_eq_inv eqn else return eqn,
`(@hott.eq %%A %%lhs %%rhs) ← infer_type eqn
    | (do e ← pp eqn, fail $ to_fmt "rewrite_core: not an equation\n:" ++ e),
abs ← kabstract tgt lhs cfg.md,
when ¬abs.has_var $ (do lhs ← pp lhs, tgt ← pp tgt,
    fail $ to_fmt "rewrite_core: could not find pattern" ++ format.line
        ++ "  " ++ lhs ++ format.line
        ++ to_fmt "in" ++ format.line
        ++ "  " ++ tgt),
let motive := lam `x binder_info.default A abs,
type_check motive <|> (do m ← pp motive, fail $
    to_fmt "rewrite_core: motive does not type check\n" ++ m),
return (abs.instantiate_var rhs, eqn, motive)

meta def mk_eq_transport (motive eqn : expr) : tactic expr :=
mk_mapp `hott.eq.transport [none, motive, none, none, eqn]

meta def rewrite_target (eqn : expr) (cfg : rewrite_cfg := {}) : tactic unit := do
tgt ← target,
(tgt', prf, motive) ← rewrite_core eqn tgt cfg,
prf ← mk_eq_inv prf,
prf ← mk_eq_transport motive prf,
apply prf

meta def rewrite_hyp (eqn : expr) (hyp : expr) (cfg : rewrite_cfg := {}) : tactic expr := do
hyp_type ← infer_type hyp,
(hyp_type', prf, motive) ← rewrite_core eqn hyp_type cfg,
prf ← mk_eq_transport motive prf,
hyp' ← assertv hyp.local_pp_name hyp_type' (prf.app hyp),
try $ clear hyp,
return hyp'

end hott

namespace tactic.interactive
open interactive interactive.types

-- TODO(gabriel): rewrite with equational lemmas

private meta def rw_goal (cfg : rewrite_cfg) (rs : list rw_rule) : tactic unit :=
rs.mmap' $ λ r, do
 save_info r.pos,
 e ← to_expr' r.rule,
 hott.rewrite_target e {cfg with symm := r.symm}

private meta def rw_hyp (cfg : rewrite_cfg) : list rw_rule → expr → tactic unit
| []      hyp := skip
| (r::rs) hyp := do
  save_info r.pos,
  e ← to_expr' r.rule,
  hyp ← hott.rewrite_hyp e hyp {cfg with symm := r.symm},
  rw_hyp rs hyp

private meta def rw_core (rs : parse rw_rules) (loca : parse location) (cfg : rewrite_cfg) : tactic unit :=
match loca with
| loc.wildcard := loca.try_apply (rw_hyp cfg rs.rules) (rw_goal cfg rs.rules)
| _            := loca.apply (rw_hyp cfg rs.rules) (rw_goal cfg rs.rules)
end >> try (tactic.reflexivity transparency.semireducible)
    >> (returnopt rs.end_pos >>= save_info <|> skip)

meta def rwr (q : parse rw_rules) (l : parse location) (cfg : rewrite_cfg := {}) : tactic unit :=
rw_core q l cfg

/-- rwr followed by assumption -/
meta def rwra (q : parse rw_rules) (l : parse location) (cfg : rewrite_cfg := {}) : tactic unit :=
rw_core q l cfg >> try assumption

end tactic.interactive