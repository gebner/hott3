/-
Copyright (c) 2017 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import .support
open tactic expr

namespace hott

private meta def open_pis : expr → tactic (expr × list expr) | e := do
e ← whnf e,
if e.is_pi then do
    x ← mk_local' e.binding_name e.binding_info e.binding_domain,
    (e, xs) ← open_pis (e.binding_body.instantiate_var x),
    return (e, x::xs)
else return (e, [])

private meta def copy_idp_lemma (cn : name) (prio : option ℕ) (pers : bool) : tactic unit := do
let rfl_lemma_name := cn <.> "_idp_to_rfl",
d ← get_decl cn,
(t, xs) ← open_pis d.type,
match t.get_app_fn with
| (const `hott.eq [u]) := do
    [A, lhs, rhs] ← return t.get_app_args,
    is_idp ← option.is_some <$> try_core (is_def_eq lhs rhs), when is_idp $ do
    let t' := pis xs (app_of_list (const ``eq [u.succ]) [A, lhs, rhs]),
    let v' := lambdas xs (app_of_list (const ``rfl [u.succ]) [A, lhs]),
    add_decl (mk_definition rfl_lemma_name d.univ_params t' v'),
    set_basic_attribute `_refl_lemma rfl_lemma_name tt,
    set_basic_attribute `simp rfl_lemma_name tt
| _ := skip
end

-- TODO(gabriel): propagate priority & persistence (currently crashes)

@[user_attribute]
meta def hsimp_attr : user_attribute := {
    name := `hsimp,
    descr := "HoTT simplification lemma (converts idp-lemmas to rfl-lemmas for dsimp)",
    after_set := some (λ n prio pers, do
        copy_idp_lemma n none pers,
        set_basic_attribute `simp n pers none),
}

end hott