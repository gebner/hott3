/-
Copyright (c) 2017 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import hott.init.meta.rewrite
open tactic expr

namespace hott

meta def simplify_plus_d (s : simp_lemmas) (to_unfold : list name := []) (e : expr) (cfg : simp_config := {}) (r : name := ``hott.eq)
                       (discharger : tactic unit := failed) : tactic (expr × expr) := do
((), e', pr) ← ext_simplify_core () cfg s (λ _, discharger)
  (λ _ s r p e, do
    e' ← s.dsimplify to_unfold e { cfg with unfold_reducible := ff, md := reducible, fail_if_unchanged := ff },
    return ((), e', none, true))
  (λ a s r p e, do
    guard $ r ≠ ``_root_.eq ∧ r ≠ ``_root_.heq,
    (e', pr) ← s.rewrite e discharger r semireducible,
    return ((), e', pr, e ≠ e'))
  r e,
return (e', pr)

meta def replace_target (new_tgt prf : expr) : tactic unit := do
prf ← mk_eq_inv prf,
tgt ← target,
mk_mapp ``hott.eq.mp [new_tgt, tgt, prf] >>= apply

meta def hsimp_target (s : simp_lemmas) (to_unfold : list name := []) (cfg : simp_config := {}) (discharger : tactic unit := failed) : tactic unit :=
do t ← target,
   (new_t, pr) ← simplify_plus_d s to_unfold t {cfg with lift_eq := ff} ``hott.eq discharger,
   replace_target new_t pr

open interactive interactive.types

section mk_simp_set
-- copy&pasted here since the core library filters out non-props...

private meta def add_simps : simp_lemmas → list name → tactic simp_lemmas
| s []      := return s
| s (n::ns) := do s' ← s.add_simp n, add_simps s' ns

private meta def report_invalid_simp_lemma {α : Type} (n : name): tactic α :=
fail format!"invalid simplification lemma '{n}' (use command 'set_option trace.simp_lemmas true' for more details)"

private meta def check_no_overload (p : pexpr) : tactic unit :=
when p.is_choice_macro $
  match p with
  | macro _ ps :=
    fail $ to_fmt "ambiguous overload, possible interpretations" ++
           format.join (ps.map (λ p, (to_fmt p).indent 4))
  | _ := failed
  end

private meta def simp_lemmas.resolve_and_add (s : simp_lemmas) (u : list name) (n : name) (ref : pexpr) : tactic (simp_lemmas × list name) :=
do
  p ← resolve_name n,
  check_no_overload p,
  -- unpack local refs
  let e := p.erase_annotations.get_app_fn.erase_annotations,
  match e with
  | const n _           :=
    (do b ← is_valid_simp_lemma_cnst n, guard b, save_const_type_info n ref, s ← s.add_simp n, return (s, u))
    <|>
    (do eqns ← get_eqn_lemmas_for tt n, guard (eqns.length > 0), save_const_type_info n ref, s ← add_simps s eqns, return (s, u))
    <|>
    (do env ← get_env, guard (env.is_projection n).is_some, return (s, n::u))
    <|>
    report_invalid_simp_lemma n
  | _ :=
    (do e ← i_to_expr_no_subgoals p, b ← is_valid_simp_lemma e, guard b, try (save_type_info e ref), s ← s.add e, return (s, u))
    <|>
    report_invalid_simp_lemma n
  end

private meta def simp_lemmas.add_pexpr (s : simp_lemmas) (u : list name) (p : pexpr) : tactic (simp_lemmas × list name) :=
match p with
| (const c [])          := simp_lemmas.resolve_and_add s u c p
| (local_const c _ _ _) := simp_lemmas.resolve_and_add s u c p
| _                     := do new_e ← i_to_expr_no_subgoals p, s ← s.add new_e, return (s, u)
end

private meta def simp_lemmas.append_pexprs : simp_lemmas → list name → list pexpr → tactic (simp_lemmas × list name)
| s u []      := return (s, u)
| s u (l::ls) := do (s, u) ← simp_lemmas.add_pexpr s u l, simp_lemmas.append_pexprs s u ls

meta def mk_simp_set_core (no_dflt : bool) (attr_names : list name) (hs : list simp_arg_type) (at_star : bool)
                          : tactic (bool × simp_lemmas × list name) :=
do (hs, gex, hex, all_hyps) ← decode_simp_arg_list hs,
   when (all_hyps ∧ at_star ∧ not hex.empty) $ fail "A tactic of the form `simp [*, -h] at *` is currently not supported",
   s      ← join_user_simp_lemmas no_dflt attr_names,
   (s, u) ← simp_lemmas.append_pexprs s [] hs,
   s      ← if not at_star ∧ all_hyps then do
              ctx ← local_context,
              let ctx := ctx.filter (λ h, h.local_uniq_name ∉ hex), -- remove local exceptions
              s.append ctx
            else return s,
   -- add equational lemmas, if any
   gex ← gex.mmap (λ n, list.cons n <$> get_eqn_lemmas_for tt n),
   return (all_hyps, simp_lemmas.erase s $ gex.join, u)

meta def mk_simp_set (no_dflt : bool) (attr_names : list name) (hs : list simp_arg_type) : tactic (simp_lemmas × list name) :=
prod.snd <$> (hott.mk_simp_set_core no_dflt attr_names hs ff)

end mk_simp_set

end hott

namespace tactic
open interactive.types interactive
open hott

namespace interactive

meta def hsimp_core_aux (cfg : simp_config) (discharger : tactic unit) (s : simp_lemmas) (u : list name) (hs : list expr) (tgt : bool) : tactic unit :=
do to_remove ← hs.mfilter $ λ h, do {
         h_type ← infer_type h,
         (do (new_h_type, pr) ← simplify_plus_d s u h_type cfg ``hott.eq discharger,
             assert h.local_pp_name new_h_type,
             mk_app ``hott.eq.mp [pr, h] >>= tactic.exact >> return tt)
         <|>
         (return ff) },
   goal_simplified ← if tgt then (hsimp_target s u cfg discharger >> return tt) <|> (return ff) else return ff,
   guard (cfg.fail_if_unchanged = ff ∨ to_remove.length > 0 ∨ goal_simplified) <|> fail "simplify tactic failed to simplify",
   to_remove.mmap' (λ h, try (tactic.clear h))

meta def hsimp_core (cfg : simp_config) (discharger : tactic unit)
                   (no_dflt : bool) (hs : list simp_arg_type) (attr_names : list name)
                   (locat : loc) : tactic unit :=
match locat with
| loc.wildcard := do (all_hyps, s, u) ← hott.mk_simp_set_core no_dflt attr_names hs tt,
                     if all_hyps then fail "hsimp does not support `at *` yet" --tactic.hsimp_all s u cfg discharger
                     else do hyps ← local_context, hsimp_core_aux cfg discharger s u hyps tt
| _            := do (s, u) ← hott.mk_simp_set no_dflt attr_names hs,
                     ns ← locat.get_locals,
                     hsimp_core_aux cfg discharger s u ns locat.include_goal
end
>> try tactic.triv >> try (tactic.reflexivity reducible)

/--
This tactic uses lemmas and hypotheses to simplify the main goal target or non-dependent hypotheses.
It has many variants.

- `hsimp` simplifies the main goal target using lemmas tagged with the attribute `[hsimp]`.

- `hsimp [h_1, ..., h_n]` simplifies the main goal target using the lemmas tagged with the attribute `[hsimp]` and the given `h_i`s.
   The `h_i`'s are terms. If a `h_i` is a definition `f`, then the equational lemmas associated with `f` are used.
   This is a convenient way to "unfold" `f`.

- `hsimp [*]` simplifies the main goal target using the lemmas tagged with the attribute `[hsimp]` and all hypotheses.
  Remark: `hsimp *` is a shorthand for `hsimp [*]`.

- `hsimp only [h_1, ..., h_n]` is like `hsimp [h_1, ..., h_n]` but does not use `[hsimp]` lemmas

- `hsimp [-id_1, ... -id_n]` simplifies the main goal target using the lemmas tagged with the attribute `[hsimp]`,
   but removes the ones named `id_i`s.

- `hsimp at h_1 ... h_n` simplifies the non dependent hypotheses `h_1 : T_1` ... `h_n : T : n`. The tactic fails if the target or another hypothesis depends on one of them.

- `hsimp at *` simplifies all the hypotheses and the target.

- `hsimp * at *` simplifies target and all (non-dependent propositional) hypotheses using the other hypotheses.

- `hsimp with attr_1 ... attr_n` simplifies the main goal target using the lemmas tagged with any of the attributes `[attr_1]`, ..., `[attr_n]` or `[hsimp]`.
-/
meta def hsimp (no_dflt : parse only_flag) (hs : parse simp_arg_list) (attr_names : parse with_ident_list)
              (locat : parse location) (cfg : simp_config_ext := {}) : tactic unit :=
hsimp_core cfg.to_simp_config cfg.discharger no_dflt hs attr_names locat

end interactive
end tactic